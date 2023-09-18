#include <flint/flint.h>
#include <flint/fmpz.h>
#include <flint/fmpz_mat.h>
#include <flint/perm.h>

void _perm_mat(fmpz_mat_t a, slong *x, slong n) {
  fmpz_mat_zero(a);
  for(slong j=0; j<n; j++) {
    fmpz_one(fmpz_mat_entry(a, j, x[j]));
  }
}
