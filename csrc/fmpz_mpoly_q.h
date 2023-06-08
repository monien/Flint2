#ifndef FMPZ_MPOLY_Q_H_
#define FMPZ_MPOLY_Q_H_

#include <stdio.h>
#include <flint/fmpz_mpoly.h>
#include <flint/fmpz_mpoly_q.h>

char*
fmpz_mpoly_q_get_str_pretty(const fmpz_mpoly_q_t x, const char ** vars, const fmpz_mpoly_ctx_t ctx);

void
fmpz_mpoly_q_fprint_pretty(FILE *out, const fmpz_mpoly_q_t f, const char ** x, const fmpz_mpoly_ctx_t ctx);

#endif
