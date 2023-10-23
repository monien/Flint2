#ifndef ARB_H_
#define ARB_H_

#include <flint/arb.h>

arf_struct * arb_midref_(arb_t x);
mag_struct * arb_radref_(arb_t x);

char * arb_get_str_(const arb_t x);
char * arb_get_strd(const arb_t x, slong digits);
char * arb_get_strn(const arb_t x, slong digits, ulong options);

#endif // ARB_H_

 
