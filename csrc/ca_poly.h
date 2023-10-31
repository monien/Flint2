#ifndef CSRC_CA_POLY_H_
#define CSRC_CA_POLY_H_

#include <stdio.h>
#include <flint/ca_poly.h>

void
ca_poly_fprint(FILE *file, const ca_poly_t poly, ca_ctx_t ctx);

char*
ca_poly_get_str(const ca_poly_t poly, ca_ctx_t ctx);

#endif // CSRC_CA_POLY_H_
