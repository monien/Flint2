#ifndef NMOD_POLY_MAT_H_
#define NMOD_POLY_MAT_H_

#include <stdio.h>

#include <flint/flint.h>
#include <flint/nmod_poly.h>
#include <flint/nmod_poly_mat.h>

char*
nmod_poly_mat_get_str(const nmod_poly_mat_t mat, const char * x);

void
nmod_poly_mat_fprint(FILE * file, const nmod_poly_mat_t mat, const char * x);

#endif // NMOD_POLY_MAT_H_
