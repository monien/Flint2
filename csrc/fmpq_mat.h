#ifndef FMPQ_MAT_H_
#define FMPQ_MAT_H_

#include <stdio.h>

#include <flint/flint.h>
#include <flint/fmpq.h>
#include <flint/fmpq_mat.h>

char*
fmpq_mat_get_str(const fmpq_mat_t mat);

int
fmpq_mat_fprint(FILE * file, const fmpq_mat_t mat);

#endif // FMPQ_MAT_H_
