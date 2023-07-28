#include <flint/d_mat.h>

double d_mat_entry_(d_mat_t a, slong i, slong j) {
  return d_mat_entry(a, i, j);
}
