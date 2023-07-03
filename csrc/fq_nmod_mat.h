#ifndef CSRC_FQ_NMOD_MAT_H_
#define CSRC_FQ_NMOD_MAT_H_

#include <stdio.h>

#include <flint/flint.h>
#include <flint/fq_nmod.h>
#include <flint/fq_nmod_mat.h>

char*
fq_nmod_mat_get_str(const fq_nmod_mat_t mat, fq_nmod_ctx_t ctx);

char*
fq_nmod_mat_get_str_pretty(const fq_nmod_mat_t mat, fq_nmod_ctx_t ctx);

#endif // FQ_NMOD_MAT_H_
