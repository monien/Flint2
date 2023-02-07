#ifndef PADIC_MAT_H_
#define PADIC_MAT_H_

#include <stdio.h>

#include <flint/flint.h>
#include <flint/padic.h>
#include <flint/padic_mat.h>

char*
padic_mat_get_str(const padic_mat_t mat);

char*
padic_mat_get_str_pretty(const padic_mat_t mat);

#endif // PADIC_MAT_H_
