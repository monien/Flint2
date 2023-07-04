#ifndef CSRC_ARB_CALC_H_
#define CSRC_ARB_CALC_H_

#include <flint/arb_calc.h>

void arf_interval_init_(arf_interval_t v);
void arf_interval_clear_(arf_interval_t v);
arf_interval_ptr _arf_interval_vec_init_(slong n);
void             _arf_interval_vec_clear_(arf_interval_ptr v, slong n);

void arf_interval_set_(arf_interval_t v, const arf_interval_t u);
void arf_interval_swap_(arf_interval_t v, arf_interval_t u);
void arf_interval_get_arb_(arb_t x, const arf_interval_t v, slong prec);

char * arf_interval_get_strd(const arf_interval_t u, const slong digits);

#endif // CSRC_ARB_CALC_H_
