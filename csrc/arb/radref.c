#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include <flint/flint.h>
#include <flint/arb.h>

#include "../arb.h"

mag_struct * arb_radref_(arb_t x) {
  return &(x->rad);
}
