#ifndef FMPZ_MAT_H_
#define FMPZ_MAT_H_

#include <stdio.h>

#include <flint/flint.h>
#include <flint/fmpz_poly.h>
#include <flint/fmpz_poly_mat.h>

void
fmpz_poly_mat_fprint(FILE * file, const fmpz_poly_mat_t A, const char * x);

#endif // FMPZ_MAT_H_
