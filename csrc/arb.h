#ifndef ARB_H_
#define ARB_H_

#include <flint/arb.h>

arf_struct * arb_midref_(arb_t x);
char * arb_get_str_(const arb_t x);
char * arb_get_strd(const arb_t x, slong digits);

#endif // ARB_H_

 
