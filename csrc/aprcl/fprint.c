#include <flint/fmpz_mod_poly.h>
#include <flint/aprcl.h>

#include "../aprcl.h"

void
unity_zp_fprint(FILE * file, const unity_zp f)
{
  flint_fprintf(file, "p = %wu; exp = %wu\n", f->p, f->exp);
  fmpz_mod_poly_fprint(file, f->poly, f->ctx);
  flint_fprintf(file, "\n");
}
