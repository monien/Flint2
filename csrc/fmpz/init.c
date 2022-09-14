#include <stdio.h>

#include <flint/flint.h>
#include <flint/fmpz.h>

void p_fmpz_init(fmpz_t x) {
#ifdef DEBUG
  flint_fprintf(stderr, "p_fmpz_init 0x%016p\n", x);
#endif
  fmpz_init(x);
}
