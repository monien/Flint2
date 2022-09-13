#include <stdio.h>

#include <flint/flint.h>
#include <flint/fmpz.h>

void p_fmpz_clear(fmpz_t x) {
  flint_fprintf(stderr, "p_fmpz_clear 0x%016p\n", x);
  fmpz_clear(x);
}
