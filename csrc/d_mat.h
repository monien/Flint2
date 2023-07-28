#ifndef CSRC_DMAT_H_
#define CSRC_DMAT_H_

#include <stdio.h>
#include <flint/d_mat.h>

double d_mat_entry_(d_mat_t a, slong i, slong j);
void d_mat_fprint(FILE *file, const d_mat_t mat);
char* d_mat_get_str(const d_mat_t mat);

#endif // CSRC_DMAT_H_
