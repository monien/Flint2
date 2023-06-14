#ifndef QFB_H_
#define QFB_H_

#include <flint/flint.h>
#include <flint/qfb.h>

void qfb_fprint(FILE * out, const qfb_t x);
char * qfb_get_str(const qfb_t x);


#endif // QFB_H_
