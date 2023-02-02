#ifndef CSRC_PADIC_POLY_H_
#define CSRC_PADIC_POLY_H_

#include <flint/padic_poly.h>

char*
padic_poly_get_str(padic_poly_t poly, padic_ctx ctx);

char*
padic_poly_get_str_pretty(padic_poly_t poly, const char *var,
			  const padic_ctx_t ctx);

#endif // CSRC_PADIC_POLY_H_
