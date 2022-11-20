#ifndef FMPQ_VEC_H_
#define FMPQ_VEC_H_

#include <stdio.h>

#include <flint/flint.h>
#include <flint/fmpq.h>
#include <flint/fmpq_vec.h>

char*
fmpq_vec_get_str(const long n, const fmpq_t vec);

#endif // FMPQ_VEC_H_
