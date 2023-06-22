#ifndef CSRC_FMPZ_MOD_POLY_FACTOR_H_
#define CSRC_FMPZ_MOD_POLY_FACTOR_H_

#include <stdio.h>

#include <flint/fmpz_mod_poly.h>
#include <flint/fmpz_mod_poly_factor.h>

void
fmpz_mod_poly_factor_fprint(FILE * out,
			    const fmpz_mod_poly_factor_t fac,
			    const fmpz_mod_ctx_t ctx);

void
fmpz_mod_poly_factor_fprint_pretty(FILE * out,
				   const fmpz_mod_poly_factor_t fac,
				   const char *var,
				   const fmpz_mod_ctx_t ctx);


char * 
fmpz_mod_poly_factor_get_str(const fmpz_mod_poly_factor_t fac,
			     const fmpz_mod_ctx_t ctx);

#endif // CSRC_FMPZ_MOD_POLY_FACTOR_H_
