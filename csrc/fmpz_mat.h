#ifndef FMPZ_MAT_H_
#define FMPZ_MAT_H_

#include <stdio.h>

#include <flint/flint.h>
#include <flint/fmpz.h>
#include <flint/fmpz_mat.h>

char*
fmpz_mat_get_str(const fmpz_mat_t mat);

char*
fmpz_mat_get_str_pretty(const fmpz_mat_t mat);

#endif // FMPZ_MAT_H_
