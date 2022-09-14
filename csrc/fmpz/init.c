#include <stdio.h>

#include <flint/flint.h>
#include <flint/fmpz.h>

<<<<<<< HEAD
void p_fmpz_init(fmpz_t x) {
#ifdef DEBUG
  flint_fprintf(stderr, "p_fmpz_init 0x%016p\n", x);
#endif
=======
void fmpz_init_(fmpz_t x) {
  flint_fprintf(stderr, "fmpz_init_ 0x%016p\n", x);
>>>>>>> 471624ab3067dcc8cfcb4e6b7f648e6cb6172ce2
  fmpz_init(x);
}
