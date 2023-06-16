#ifndef ACB_MODULAR_H_
#define ACB_MODULAR_H_

#include <flint/acb_modular.h>

void psl2z_init_(psl2z_t g);
void psl2z_clear_(psl2z_t g);
void psl2z_swap_(psl2z_t f, psl2z_t g);
void psl2z_set_(psl2z_t h, const psl2z_t g);
void psl2z_one_(psl2z_t g);
int psl2z_equal_(const psl2z_t f, const psl2z_t g);
int psl2z_is_one_(const psl2z_t f);
  
char * psl2z_get_str(const psl2z_t x);

#endif ACB_MODULAR_H_
