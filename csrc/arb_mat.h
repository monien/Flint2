#ifndef CSRC_ARB_MAT_H_
#define CSRC_ARB_MAT_H_

#include <stdio.h>

#include <flint/arb_mat.h>

arb_ptr arb_mat_entry_(arb_mat_t mat, slong i, slong j);

char* arb_mat_get_strd(const arb_mat_t mat, slong digits);
char* arb_mat_get_strn(const arb_mat_t mat, slong digits, ulong options);

void
arb_mat_fprintn(FILE * file, const arb_mat_t mat, slong digits, ulong options);

#endif // CSRC_ARB_MAT_H_
