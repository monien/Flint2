#include <stdio.h>
#include <flint/double_interval.h>

#include "../double_interval.h"

void di_fprint(FILE * out, const di_t x) {
  flint_fprintf(stderr, "[%.17g, %.17g]", x.a, x.b);
  flint_fprintf(out, "[%.17g, %.17g]", x.a, x.b);
}
