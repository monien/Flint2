#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include <flint/flint.h>

#include "../qqbar.h"

char*
qqbar_get_str(const qqbar_t x)
{
   char * buffer = NULL;
   size_t buffer_size = 0;

   FILE * out = open_memstream(&buffer, &buffer_size);

   qqbar_fprint(out, x);

   fclose(out);

   return buffer;
}
