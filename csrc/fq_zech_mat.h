#ifndef CSRC_FQ_ZECH_MAT_H_
#define CSRC_FQ_ZECH_MAT_H_

#include <stdio.h>

#include <flint/flint.h>
#include <flint/fq_zech.h>
#include <flint/fq_zech_mat.h>

char*
fq_zech_mat_get_str(const fq_zech_mat_t mat, fq_zech_ctx_t ctx);

char*
fq_zech_mat_get_str_pretty(const fq_zech_mat_t mat, fq_zech_ctx_t ctx);

#endif // FQ_ZECH_MAT_H_
