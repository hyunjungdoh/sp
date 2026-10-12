#include "Harness.hpp"

#include <cstdlib>
#include <iostream>
#include <string>

namespace {

int fail(const std::string &msg) {
  std::cerr << msg << "\n";
  return 1;
}

} // namespace

int main() {
  chain::EntryGroup jpeg;
  jpeg.chop = "jpeg_read_scanlines";
  jpeg.entries = {"TIFFReadScanline", "TIFFReadEncodedStrip"};
  jpeg.initial = {"TIFFReadScanline"};
  jpeg.flow = true;
  chain::Input buf;
  buf.func = "TIFFReadScanline";
  buf.arg = 1;
  buf.chopArg = 0;
  chain::Input row;
  row.func = "TIFFReadScanline";
  row.arg = 2;
  row.chopArg = 1;
  jpeg.inputs = {buf, row};

  chain::EntryGroup empty;
  empty.chop = "jpeg_write_scanlines";

  realdef::UseDef use;
  use.use = "load i8*";
  realdef::Def store;
  store.kind = "store";
  store.func = "jcopy_sample_rows";
  store.file = "jutils.c";
  store.line = 112;
  realdef::Def ext;
  ext.kind = "external";
  ext.func = "jpeg_read_scanlines";
  ext.arg = 0;
  ext.chopArg = 0;
  realdef::Def other;
  other.kind = "external";
  other.func = "jpeg_start_decompress";
  other.arg = 1;
  realdef::Def init;
  init.kind = "init";
  init.func = "jpeg_std_error";
  init.file = "jerror.c";
  init.line = 1;
  use.defs = {store, ext, other, init};

  auto out = harness::specs({jpeg, empty}, {use});
  if (out.size() != 1)
    return fail("a chop with no entry is not a query");
  if (out[0].chop != "jpeg_read_scanlines")
    return fail("chop");
  if (out[0].calls.size() != 1 || out[0].calls[0] != "TIFFReadScanline")
    return fail("the formula calls the maximal entry");
  if (out[0].symbolic.size() != 1 || out[0].symbolic[0].func != "TIFFReadScanline" ||
      out[0].symbolic[0].arg != 1 || out[0].symbolic[0].chopArg != 0)
    return fail("symbolic input is the entry parameter that reaches the named chop argument");
  if (out[0].writes.size() != 2 || out[0].writes[0].kind != "store" || out[0].writes[1].kind != "init")
    return fail("store and initializer stay transitions");
  if (out[0].uses.size() != 1)
    return fail("use");

  const std::string text = harness::format(out);
  if (text.find("symbolic TIFFReadScanline arg 1 chop-arg 0\n") == std::string::npos)
    return fail("format symbolic");
  if (text.find("jpeg_start_decompress") != std::string::npos)
    return fail("another function's parameter is not this query");
  if (text.find("write store jcopy_sample_rows jutils.c:112\n") == std::string::npos)
    return fail("format write");
  if (text.find("jpeg_write_scanlines") != std::string::npos)
    return fail("empty chop stays out of the text");
  return 0;
}
