#ifndef CSRC_PADIC_MAT_H_
#define CSRC_PADIC_MAT_H_

#include <stdio.h>

#include <flint/flint.h>
#include <flint/padic.h>
#include <flint/padic_mat.h>

char*
padic_mat_get_str(const padic_mat_t mat, padic_ctx_t ctx);

char*
padic_mat_get_str_pretty(const padic_mat_t mat, padic_ctx_t ctx);

#endif // PADIC_MAT_H_
