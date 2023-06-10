#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include <flint/flint.h>
#include <flint/arb.h>

#include "../acb.h"

char*
acb_get_strn(const acb_t x, slong digits, ulong flags)
{
   char * buffer = NULL;
   size_t buffer_size = 0;

   FILE * out = open_memstream(&buffer, &buffer_size);

   acb_fprintn(out, x, digits, flags);

   fclose(out);

   return buffer;
}
