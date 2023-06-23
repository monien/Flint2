#ifndef CSRC_DOUBLE_INTERVAL_H_
#define CSRC_DOUBLE_INTERVAL_H_

#include <stdio.h>
#include <flint/double_interval.h>

void
di_fprint(FILE * out, const di_t x);

char *
di_get_str(const di_t x);

#endif // CSRC_DOUBLE_INTERVAL_H_
