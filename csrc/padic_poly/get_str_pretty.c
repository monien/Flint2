#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include <flint/padic_poly.h>

char*
padic_poly_get_str_pretty(padic_poly_t poly, const char *var, const padic_ctx_t ctx)
{
  char* buffer = NULL;
  size_t bufferSize = 0;
  FILE* out = open_memstream(&buffer, &bufferSize);
  padic_poly_fprint_pretty(out, poly, var, ctx);
  fclose(out);
  return buffer;
}
