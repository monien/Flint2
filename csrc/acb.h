#ifndef ACB_H_
#define ACB_H_

#include <flint/acb.h>

char* acb_get_str (const acb_t x);
char* acb_get_strd(const acb_t x, slong digits);
char* acb_get_strn(const acb_t x, slong digits, ulong flags);

#endif // ACB_H_

 
