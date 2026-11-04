/* Minimal libheif decode of a memory buffer — for ASan PoC checks. */
#include <stdio.h>
#include <stdlib.h>
#include <libheif/heif.h>

static unsigned char *slurp(const char *path, size_t *n) {
  FILE *f = fopen(path, "rb");
  if (!f) return NULL;
  fseek(f, 0, SEEK_END);
  long sz = ftell(f);
  fseek(f, 0, SEEK_SET);
  unsigned char *b = malloc((size_t)sz);
  if (!b) { fclose(f); return NULL; }
  if (fread(b, 1, (size_t)sz, f) != (size_t)sz) { free(b); fclose(f); return NULL; }
  fclose(f);
  *n = (size_t)sz;
  return b;
}

int main(int argc, char **argv) {
  if (argc < 2) {
    fprintf(stderr, "usage: %s file.heic\n", argv[0]);
    return 2;
  }
  size_t n = 0;
  unsigned char *buf = slurp(argv[1], &n);
  if (!buf) { perror(argv[1]); return 1; }

  heif_context *ctx = heif_context_alloc();
  struct heif_error err = heif_context_read_from_memory_without_copy(ctx, buf, n, NULL);
  if (err.code != heif_error_Ok) {
    fprintf(stderr, "read: %s\n", err.message);
    heif_context_free(ctx); free(buf); return 1;
  }

  heif_image_handle *handle = NULL;
  err = heif_context_get_primary_image_handle(ctx, &handle);
  if (err.code != heif_error_Ok) {
    fprintf(stderr, "primary: %s\n", err.message);
    heif_context_free(ctx); free(buf); return 1;
  }

  heif_image *img = NULL;
  err = heif_decode_image(handle, &img, heif_colorspace_undefined,
                          heif_chroma_undefined, NULL);
  fprintf(stderr, "decode: code=%d sub=%d msg=%s\n",
          err.code, err.subcode, err.message ? err.message : "");
  if (img) heif_image_release(img);
  heif_image_handle_release(handle);
  heif_context_free(ctx);
  free(buf);
  return err.code != heif_error_Ok;
}
