#include <stdio.h>

#include <flint/flint.h>
#include <flint/fmpz.h>
#include <flint/fmpzi.h>

#include "../fmpzi.h"

void
fmpzi_fprint(FILE * file, const fmpzi_t x)
{
  fmpz_fprint(file, fmpzi_realref(x));
  if (fmpz_sgn(fmpzi_imagref(x)) >= 0)
    flint_fprintf(file, "+");
  fmpz_fprint(file, fmpzi_imagref(x));
  flint_fprintf(file, "*I");
}

