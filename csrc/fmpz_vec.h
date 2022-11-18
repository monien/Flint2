#ifndef FMPZ_VEC_H_
#define FMPZ_VEC_H_

#include <stdio.h>

#include <flint/flint.h>
#include <flint/fmpz.h>
#include <flint/fmpz_vec.h>

char*
fmpz_vec_get_str(const long n, const fmpz_t vec);

#endif // FMPZ_VEC_H_
