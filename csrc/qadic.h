#ifndef CSRC_QADIC_H_
#define CSRC_QADIC_H_

#include <flint/quadic.h>

char * qadic_get_str(char * str, quadic_t x, quadic_ctx_t ctx);

char*
padic_poly_get_str_pretty(padic_poly_t poly, const char *var,
			  const padic_ctx_t ctx);

#endif // CSRC_QADIC_H_
