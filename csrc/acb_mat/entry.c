#include <flint/acb_mat.h>

acb_ptr acb_mat_entry_(acb_mat_t mat, slong i, slong j) {
  return mat->rows[i] + j;
}
