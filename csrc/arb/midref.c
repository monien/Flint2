#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include <flint/flint.h>
#include <flint/arb.h>

#include "../arb.h"

arf_struct * arb_midref_(arb_t x) {
  return &(x->mid);
}
