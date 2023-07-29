#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include <flint/flint.h>
#include <flint/arb.h>

#include "../arb.h"

char*
arb_get_strn(const arb_t x, slong digits, ulong options)
{
   char * buffer = NULL;
   size_t buffer_size = 0;

   FILE * out = open_memstream(&buffer, &buffer_size);

   arb_fprintn(out, x, digits, options);

   fclose(out);

   return buffer;
}
