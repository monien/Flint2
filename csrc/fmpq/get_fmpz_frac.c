#include "../fmpq.h"

void fmpq_get_fmpz_frac(fmpz_t num, fmpz_t den, fmpq_t x) {
  fmpz_set(num, fmpq_numref(x));
  fmpz_set(den, fmpq_denref(x));
}
