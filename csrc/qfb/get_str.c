#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include <flint/flint.h>

#include "../qfb.h"

char*
qfb_get_str(const qfb_t x)
{
   char * buffer = NULL;
   size_t buffer_size = 0;

   FILE * out = open_memstream(&buffer, &buffer_size);

   qfb_fprint(out, x);

   fclose(out);

   return buffer;
}
