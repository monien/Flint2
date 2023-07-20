#include "../fmpq.h"

#include <flint/flint.h>

void fmpq_mediant(fmpq_t x, fmpq_t l, fmpq_t r) {

  fmpz_t num, den;

  fmpz_init(num);
  fmpz_init(den);

  fmpz_add(num, fmpq_numref(l), fmpq_numref(r));
  fmpz_add(den, fmpq_denref(l), fmpq_denref(r));
  
  fmpq_set_fmpz_frac(x, num, den);

  fmpz_clear(num);
  fmpz_clear(den);
 
}
