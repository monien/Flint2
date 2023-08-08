#ifndef CSRC_PULLBACK_H_
#define CSRC_PULLBACK_H_

#include <flint/acb_modular.h>
#include <flint/fmpz.h>

typedef struct {
  fmpz * letters;
  slong alloc;
} psl2z_word_struct;

typedef psl2z_word_struct psl2z_word_t[1];

void psl2z_word_init(psl2z_word_t word); 
void psl2z_word_clear(psl2z_word_t word);

void psl2z_normal_form(psl2z_t x);

void psl2z_get_word(psl2z_word_t word, psl2z_t gamma);
void psl2z_set_word(psl2z_t gamma, psl2z_word_t word);

void psl2z_word_fprint(FILE * file, psl2z_word_t word);
void psl2z_word_print(psl2z_word_t word);
char * psl2z_word_get_str(psl2z_word_t word);

void psl2z_word_fprint_pretty(FILE * file, psl2z_word_t word);
void psl2z_word_print_pretty(psl2z_word_t word);
char * psl2z_word_get_str_pretty(psl2z_word_t word);

void _perm_set_word(slong *x, slong *s, slong *t, slong n, psl2z_word_t word);
  
#endif // CSRC_PULLBACK_H_
