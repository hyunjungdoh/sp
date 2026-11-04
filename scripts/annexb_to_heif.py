#!/usr/bin/env python3
"""Wrap an annex-B HEVC bitstream in a minimal single-image HEIF/HEIC.

Does not re-encode: start-code NALs become length-prefixed sample data and
parameter sets (VPS/SPS/PPS) are copied into hvcC. For downstream harnesses
that feed libheif → libde265, this is the seed shape matching
heif_context_read_from_memory (unlike raw dec265 PoCs).

Usage:
  annexb_to_heif.py <in.bin> <out.heic> [width] [height]
  annexb_to_heif.py <in.bin> <out.heic> --hvcc <clean.h265> [width] [height]

With --hvcc, parameter sets for the HEIF hvcC box come from the clean
bitstream (so libheif SPS checks pass), while the PoC's NALs are all placed
in mdat for libde265.
"""
from __future__ import annotations

import struct
import sys
from pathlib import Path


def split_annexb(data: bytes) -> list[bytes]:
    starts: list[tuple[int, int]] = []
    i = 0
    n = len(data)
    while i < n:
        if i + 4 <= n and data[i : i + 4] == b"\x00\x00\x00\x01":
            starts.append((i, 4))
            i += 4
        elif i + 3 <= n and data[i : i + 3] == b"\x00\x00\x01":
            starts.append((i, 3))
            i += 3
        else:
            i += 1
    nals: list[bytes] = []
    for k, (off, sc) in enumerate(starts):
        end = starts[k + 1][0] if k + 1 < len(starts) else n
        nal = data[off + sc : end]
        if nal:
            nals.append(nal)
    return nals


def nal_type(nal: bytes) -> int:
    return (nal[0] >> 1) & 0x3F


def box(typ: bytes, payload: bytes) -> bytes:
    assert len(typ) == 4
    return struct.pack(">I", 8 + len(payload)) + typ + payload


def full_box(typ: bytes, version: int, flags: int, payload: bytes) -> bytes:
    return box(typ, struct.pack(">I", (version << 24) | flags) + payload)


def build_hvcc(vps: list[bytes], sps: list[bytes], pps: list[bytes]) -> bytes:
    # ISO/IEC 14496-15 HEVCDecoderConfigurationRecord with safe defaults.
    # lengthSizeMinusOne = 3 → 4-byte NAL lengths (matches libheif plugin).
    body = bytearray()
    body.append(1)  # configurationVersion
    body.append(1)  # general_profile_space/tier/idc placeholder
    body += b"\x00\x00\x00\x00"  # profile_compatibility
    body += b"\x00\x00\x00\x00\x00\x00"  # constraint indicator
    body.append(120)  # level_idc
    body += struct.pack(">H", 0xF000)  # reserved + min_spatial_segmentation
    body.append(0xFC)  # reserved + parallelismType
    body.append(0xFC)  # reserved + chromaFormat
    body.append(0xF8)  # reserved + bitDepthLumaMinus8
    body.append(0xF8)  # reserved + bitDepthChromaMinus8
    body += struct.pack(">H", 0)  # avgFrameRate
    body.append(0x0F)  # constFR=0, tempLayers=0, nested=1, lengthSizeMinusOne=3
    arrays = [(32, vps), (33, sps), (34, pps)]
    present = [(t, xs) for t, xs in arrays if xs]
    body.append(len(present))
    for ntype, xs in present:
        body.append(0x80 | (ntype & 0x3F))  # array_completeness=1
        body += struct.pack(">H", len(xs))
        for nal in xs:
            body += struct.pack(">H", len(nal))
            body += nal
    return bytes(body)


def build_heif(
    nals: list[bytes],
    width: int,
    height: int,
    hvcc_nals: list[bytes] | None = None,
) -> bytes:
    if hvcc_nals is not None:
        # Benign hvcC; PoC bitstream (all NALs) in the sample.
        vps = [n for n in hvcc_nals if nal_type(n) == 32]
        sps = [n for n in hvcc_nals if nal_type(n) == 33]
        pps = [n for n in hvcc_nals if nal_type(n) == 34]
        sample_nals = nals
    else:
        vps = [n for n in nals if nal_type(n) == 32]
        sps = [n for n in nals if nal_type(n) == 33]
        pps = [n for n in nals if nal_type(n) == 34]
        sample_nals = (
            [n for n in nals if nal_type(n) not in (32, 33, 34)]
            if (vps or sps or pps)
            else nals
        )
        if not sample_nals:
            sample_nals = nals
    mdat_payload = b"".join(struct.pack(">I", len(n)) + n for n in sample_nals)
    hvcc = build_hvcc(vps or nals[:1], sps or [], pps or [])

    ftyp = box(
        b"ftyp",
        b"heic" + struct.pack(">I", 0) + b"mif1heichevc",
    )

    # Fixed layout: meta then mdat. iloc offset is absolute file offset of sample.
    # We build meta with a placeholder offset, then patch.
    ispe = full_box(b"ispe", 0, 0, struct.pack(">II", width, height))
    hvcC = box(b"hvcC", hvcc)
    ipco = box(b"ipco", ispe + hvcC)
    # item 1 → properties 1 (ispe), 2 (hvcC)
    # ipma v0: entry_count(32), item_ID(16), assoc_count(8), then
    # essential(1)+property_index(7) per association.
    ipma = full_box(
        b"ipma",
        0,
        0,
        struct.pack(">I", 1)
        + struct.pack(">HB", 1, 2)
        + bytes([0x80 | 1, 0x80 | 2]),
    )
    iprp = box(b"iprp", ipco + ipma)

    hdlr = full_box(b"hdlr", 0, 0, b"\x00\x00\x00\x00" + b"pict" + b"\x00" * 12 + b"\x00")
    pitm = full_box(b"pitm", 0, 0, struct.pack(">H", 1))
    # infe v2: item_ID(16), protection(16), item_type(4cc), name (nul)
    infe = full_box(b"infe", 2, 0, struct.pack(">HH", 1, 0) + b"hvc1" + b"\x00")
    iinf = full_box(b"iinf", 0, 0, struct.pack(">H", 1) + infe)

    # iloc version 1, offset_size=4, length_size=4, base_offset_size=0
    # patch offset later
    iloc_inner = struct.pack(
        ">BBH",
        (4 << 4) | 4,  # offset_size | length_size
        (0 << 4) | 0,  # base_offset_size | index_size
        1,  # item_count
    )
    iloc_inner += struct.pack(">HHHH", 1, 0, 0, 1)  # item_id, construction, data_ref, extent_count
    iloc_inner += struct.pack(">II", 0, len(mdat_payload))  # extent_offset, extent_length
    iloc = full_box(b"iloc", 1, 0, iloc_inner)

    meta_payload = hdlr + pitm + iloc + iinf + iprp
    meta = full_box(b"meta", 0, 0, meta_payload)
    mdat = box(b"mdat", mdat_payload)

    # Absolute sample offset = ftyp + meta + mdat header; patch iloc extent.
    sample_off = len(ftyp) + len(meta) + 8
    meta_body = bytearray(meta)
    iloc_at = meta_body.find(b"iloc")
    if iloc_at < 4:
        raise RuntimeError("iloc missing")
    box_start = iloc_at - 4
    box_size = struct.unpack_from(">I", meta_body, box_start)[0]
    ext_off_pos = box_start + box_size - 8
    meta_body[ext_off_pos : ext_off_pos + 4] = struct.pack(">I", sample_off)
    meta = bytes(meta_body)
    return ftyp + meta + mdat


def main() -> None:
    args = sys.argv[1:]
    if len(args) < 2:
        print(__doc__, file=sys.stderr)
        sys.exit(2)
    inp, out = Path(args[0]), Path(args[1])
    hvcc_path = None
    rest: list[str] = []
    i = 2
    while i < len(args):
        if args[i] == "--hvcc" and i + 1 < len(args):
            hvcc_path = Path(args[i + 1])
            i += 2
        else:
            rest.append(args[i])
            i += 1
    width = int(rest[0]) if len(rest) > 0 else 64
    height = int(rest[1]) if len(rest) > 1 else 64
    data = inp.read_bytes()
    nals = split_annexb(data)
    if not nals:
        print(f"{inp}: no annex-B NALs found", file=sys.stderr)
        sys.exit(1)
    hvcc_nals = split_annexb(hvcc_path.read_bytes()) if hvcc_path else None
    heif = build_heif(nals, width, height, hvcc_nals)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_bytes(heif)
    extra = f" hvcc={hvcc_path.name}" if hvcc_path else ""
    print(f"{inp.name}: {len(nals)} NALs -> {out} ({len(heif)} bytes){extra}")


if __name__ == "__main__":
    main()
