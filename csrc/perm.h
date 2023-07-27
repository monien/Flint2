#ifndef CSRC_PERM_H_
#define CSRC_PERM_H_

#include <flint/fmpz.h>
#include <flint/perm.h>

void _perm_order(fmpz_t order, slong *x, slong n);

void psl2z_get_word(psl2z_word_t word, psl2z_t x);
void psl2z_set_word(psl2z_t x, psl2z_word_t word);

void _perm_set_word(slong *x, slong *s, slong *t, slong n, psl2z_word_t word);

void _perm_fprint_pretty(FILE *out, slong *x, slong n);
void _perm_print_pretty(slong *x, slong n);
char * _perm_get_str_pretty(slong *x, slong n);

#endif // CSRC_PERM_H_
