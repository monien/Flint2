#ifndef CSRC_PULLBACK_H_
#define CSRC_PULLBACK_H_

#include <flint/acb_modular.h>

typedef struct {
  fmpz * letters;
  slong alloc;
} psl2z_word_struct;

typedef psl2z_word_struct psl2z_word_t[1];

void psl2z_word_init(psl2z_word_t word); 
void psl2z_word_clear(psl2z_word_t word);
void psl2z_word_fprint(FILE * file, psl2z_word_t word);
void psl2z_word_print(psl2z_word_t word);
char * psl2z_word_get_str(psl2z_word_t word);
void psl2z_to_word(psl2z_word_t word, psl2z_t gamma);

#endif // CSRC_PULLBACK_H_
