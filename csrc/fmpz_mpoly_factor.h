#ifndef CSRC_FMPZ_MPOLY_FACTOR_H_
#define CSRC_FMPZ_MPOLY_FACTOR_H_

#include <stdio.h>
#include <flint/fmpz_mpoly_factor.h>

void
fmpz_mpoly_factor_fprint_pretty(FILE *file,
				const fmpz_mpoly_factor_t f,
                                const char ** vars,
				const fmpz_mpoly_ctx_t ctx);

char*
fmpz_mpoly_factor_get_str_pretty(const fmpz_mpoly_factor_t f,
				 const char ** vars,
				 const fmpz_mpoly_ctx_t ctx);

#endif 
