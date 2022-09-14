#include <stdio.h>

#include <flint/flint.h>
#include <flint/fmpz.h>
#include <flint/fmpz_factor.h>

#include "../fmpz_factor.h"

void fmpz_factor_clear_(fmpz_factor_t x) {
  flint_fprintf(stderr, "p_fmpz_factor_init 0x%016p\n", x);
  fmpz_factor_clear(x);
}
