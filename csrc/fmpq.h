#ifndef FMPQ_H_
#define FMPQ_H_

#include <flint/fmpz.h>
#include <flint/fmpq.h>

void fmpq_get_fmpz_frac(fmpz_t num, fmpz_t den, fmpq_t r);
void fmpq_mediant(fmpq_t x, fmpq_t l, fmpq_t r);

slong fmpq_get_cfrac_st(fmpz *c, fmpq_t rem, const fmpq_t x, slong n);
void  fmpq_set_cfrac_st(fmpq_t x, const fmpz *c, slong n);

#endif // FMPQ_H_
