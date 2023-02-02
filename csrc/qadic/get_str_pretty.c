#include <limits.h>
#include <string.h>

#include <flint/flint.h>
#include <flint/qadic.h>

char *
qadic_get_str_pretty (const qadic_t op, const qadic_ctx_t ctx) {
  char* buffer = NULL;
  size_t bufferSize = 0;
  FILE* out = open_memstream(&buffer, &bufferSize);
  qadic_fprint_pretty(out, op, ctx);
  fclose(out);
  return buffer;
}
