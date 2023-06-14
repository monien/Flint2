#ifndef QQBAR_H_
#define QQBAR_H_

#include <flint/flint.h>
#include <flint/qqbar.h>

void qqbar_fprint(FILE * out, const qqbar_t x);
void qqbar_fprintn(FILE * out, const qqbar_t x, slong n);
void qqbar_fprintnd(FILE * out, const qqbar_t x, slong n);

char * qqbar_get_str(const qqbar_t x);
char * qqbar_get_strn(const qqbar_t x, slong digits);
char * qqbar_get_strnd(const qqbar_t x, slong digits);

#endif // QQBAR_H_
