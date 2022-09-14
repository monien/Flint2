#include <stdio.h>

#include <flint/flint.h>
#include <flint/fmpz.h>

void fmpz_clear_(fmpz_t x) {
  flint_fprintf(stderr, "fmpz_clear_ 0x%016p\n", x);
  fmpz_clear(x);
}
