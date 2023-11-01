#ifndef CA_MAT_H_
#define CA_MAT_H_

#include <stdio.h>
#include <flint/flint.h>
#include <flint/ca.h>
#include <flint/ca_mat.h>

char*
ca_mat_get_str(const ca_mat_t mat, ca_ctx_t ctx);

void
ca_mat_fprint(FILE *file, const ca_mat_t mat, ca_ctx_t ctx);

#endif // CA_MAT_H_
