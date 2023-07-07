#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include <flint/flint.h>
#include <flint/fmpzi.h>

#include "../fmpzi.h"

char*
fmpzi_get_str(const fmpzi_t z)
{
   char * buffer = NULL;
   size_t buffer_size = 0;

   FILE * out = open_memstream(&buffer, &buffer_size);

   fmpzi_fprint(out, z);

   fclose(out);

   return buffer;
}
