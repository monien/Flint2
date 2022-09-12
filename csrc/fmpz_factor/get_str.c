#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include <flint/flint.h>
#include <flint/fmpz.h>
#include <flint/fmpz_factor.h>

#include "../fmpz_factor.h"

char*
fmpz_factor_get_str(const fmpz_factor_t factor)
{
   char * buffer = NULL;
   size_t buffer_size = 0;

   FILE * out = open_memstream(&buffer, &buffer_size);

   fmpz_factor_fprint(out, factor);

   fclose(out);

   return buffer;
}
