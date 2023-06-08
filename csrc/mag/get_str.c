#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include <flint/flint.h>
#include <flint/mag.h>

#include "../mag.h"

char*
mag_get_str(const mag_t x)
{
   char * buffer = NULL;
   size_t buffer_size = 0;

   FILE * out = open_memstream(&buffer, &buffer_size);

   mag_fprint(out, x);

   fclose(out);

   return buffer;
}
