#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include <flint/padic_poly.h>

char*
padic_poly_get_str(padic_poly_t poly, const padic_ctx_t ctx)
{
  char* buffer = NULL;
  size_t bufferSize = 0;
  FILE* out = open_memstream(&buffer, &bufferSize);
  padic_poly_fprint(out, poly, ctx);
  fclose(out);
  return buffer;
}
