#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include <flint/flint.h>
#include <flint/arb.h>

#include "../arb.h"

char*
arb_get_strd(const arb_t x, slong digits)
{
   char * buffer = NULL;
   size_t buffer_size = 0;

   FILE * out = open_memstream(&buffer, &buffer_size);

   arb_fprintd(out, x, digits);

   fclose(out);

   return buffer;
}
