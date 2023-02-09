#ifndef FMPQ_H_
#define FMPQ_H_

#include <flint/fmpz.h>
#include <flint/fmpq.h>

void fmpq_get_fmpz_frac(fmpz_t num, fmpz_t den, fmpq_t r);

#endif // FMPQ_H_
