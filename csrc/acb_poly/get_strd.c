#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include <flint/flint.h>
#include <flint/acb_poly.h>

#include "../arb.h"

char*
acb_poly_get_strd(const acb_poly_t x, slong digits)
{
   char * buffer = NULL;
   size_t buffer_size = 0;

   FILE * out = open_memstream(&buffer, &buffer_size);

   acb_poly_fprintd(out, x, digits);

   fclose(out);

   return buffer;
}
