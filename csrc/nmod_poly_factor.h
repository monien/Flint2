#ifndef CSRC_NMOD_POLY_FACTOR_H_
#define CSRC_NMOD_POLY_FACTOR_H_

#include <stdio.h>
#include <flint/flint.h>
#include <flint/nmod_poly_factor.h>

void
nmod_poly_factor_fprint(FILE * file,
			const nmod_poly_factor_t fac);

void
nmod_poly_factor_fprint_pretty(FILE * file,
			       const nmod_poly_factor_t fac,
			       const char *var);

char*
nmod_poly_factor_get_str(const nmod_poly_factor_t fac);

char*
nmod_poly_factor_get_str_pretty(const nmod_poly_factor_t fac, const char *var);

#endif // CSRC_NMOD_POLY_FACTOR_H_

 
