#ifndef FMPZ_FACTOR_H_
#define FMPZ_FACTOR_H_

#include <stdio.h>

#include <flint/flint.h>
#include <flint/fmpz.h>
#include <flint/fmpz_factor.h>

void
fmpz_factor_fprint(FILE * out, const fmpz_factor_t factor);

char*
fmpz_factor_get_str(const fmpz_factor_t factor);

#endif // FMPZ_FACTOR_H_
