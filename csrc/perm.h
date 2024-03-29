#ifndef CSRC_PERM_H_
#define CSRC_PERM_H_

#include <flint/fmpz.h>
#include <flint/perm.h>

void _perm_order(fmpz_t order, slong *x, slong n);
void _perm_power(slong *x_p, slong *x, slong p, slong n);

void _perm_mat(fmpz_mat_t a, slong *x, slong n);

void _perm_fprint_pretty(FILE *out, slong *x, slong n);
void _perm_print_pretty(slong *x, slong n);
char * _perm_get_str_pretty(slong *x, slong n);

#endif // CSRC_PERM_H_
