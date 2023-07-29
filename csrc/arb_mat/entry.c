#include <flint/arb_mat.h>

arb_ptr arb_mat_entry_(arb_mat_t mat, slong i, slong j) {
  return mat->rows[i] + j;
}
