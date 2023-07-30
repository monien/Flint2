#ifndef CSRC_ACB_MAT_H_
#define CSRC_ACB_MAT_H_

#include <stdio.h>

#include <flint/acb_mat.h>

acb_ptr acb_mat_entry_(acb_mat_t mat, slong i, slong j);

char* acb_mat_get_strd(const acb_mat_t mat, slong digits);
char* acb_mat_get_strn(const acb_mat_t mat, slong digits, ulong options);

void
acb_mat_fprintn(FILE * file, const acb_mat_t mat, slong digits, ulong options);

#endif // CSRC_ACB_MAT_H_
