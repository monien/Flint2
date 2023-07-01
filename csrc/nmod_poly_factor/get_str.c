#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include <flint/flint.h>
#include <flint/nmod_poly_factor.h>

#include "../nmod_poly_factor.h"

char*
nmod_poly_factor_get_str(const nmod_poly_factor_t fac)
{
   char * buffer = NULL;
   size_t buffer_size = 0;

   FILE * out = open_memstream(&buffer, &buffer_size);

   nmod_poly_factor_fprint(out, fac);

   fclose(out);

   return buffer;
}
