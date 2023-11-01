#ifndef CA_EXT_H_
#define CA_EXT_H_

#include <flint/flint.h>

#include <flint/ca.h>
#include <flint/ca_ext.h>

void ca_ext_fprint(FILE *out, const ca_ext_t x, ca_ctx_t ctx);

char * ca_ext_get_str(const ca_ext_t x, ca_ctx_t ctx);

#endif // CA_EXT_H_
