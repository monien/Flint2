#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include <flint/double_interval.h>

#include "../double_interval.h"

char*
di_get_str(const di_t x)
{
   char * buffer = NULL;
   size_t buffer_size = 0;
   
   FILE * out = open_memstream(&buffer, &buffer_size);

   di_fprint(out, x);

   fclose(out);

   flint_fprintf(stderr, "[%.17g, %.17g]", x.a, x.b);
   
   return buffer;
}
