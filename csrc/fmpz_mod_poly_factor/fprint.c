#include <stdio.h>

#include <flint/fmpz_mod_poly.h>
#include <flint/fmpz_mod_poly_factor.h>

#include "../fmpz_mod_poly_factor.h"

void
fmpz_mod_poly_factor_fprint(FILE * out,
			    const fmpz_mod_poly_factor_t fac,
			    const fmpz_mod_ctx_t ctx)
{
  slong i;
  
  for (i = 0; i < fac->num; i++)
    {
      fmpz_mod_poly_fprint(out, fac->poly + i, ctx);
      flint_fprintf(out, " ^ %wd\n", fac->exp[i]);
    }
}
