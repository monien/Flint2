#ifndef FMPZ_MAT_H_
#define FMPZ_MAT_H_

#include <stdio.h>

#include <flint/flint.h>
#include <flint/fq.h>
#include <flint/fq_mat.h>

char*
fq_mat_get_str(const fq_mat_t mat, const fq_ctx_t ctx);

char*
fq_mat_get_str_pretty(const fq_mat_t mat, const fq_ctx_t ctx);

#endif // FQ_MAT_H_
