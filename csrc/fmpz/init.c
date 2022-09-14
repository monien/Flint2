#include <stdio.h>

#include <flint/flint.h>
#include <flint/fmpz.h>

void fmpz_init_(fmpz_t x) {
  flint_fprintf(stderr, "fmpz_init_ 0x%016p\n", x);
  fmpz_init(x);
}
