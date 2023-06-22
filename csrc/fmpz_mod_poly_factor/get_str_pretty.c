#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include <flint/fmpz_mod_poly.h>
#include <flint/fmpz_mod_poly_factor.h>

#include "../fmpz_mod_poly_factor.h"

char * 
fmpz_mod_poly_factor_get_str_pretty(const fmpz_mod_poly_factor_t fac,
				    const char * var, 
				    const fmpz_mod_ctx_t ctx)
{
   char * buffer = NULL;
   size_t buffer_size = 0;

   FILE * out = open_memstream(&buffer, &buffer_size);

   fmpz_mod_poly_factor_fprint_pretty(out, fac, var, ctx);

   fclose(out);

   return buffer;
}
