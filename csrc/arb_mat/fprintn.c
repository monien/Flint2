#include <flint/arb.h>
#include <flint/arb_mat.h>

#include "../arb_mat.h"

void
arb_mat_fprintn(FILE * file, const arb_mat_t mat, slong digits, ulong options) {
  slong i, j;
  
  for (i = 0; i < arb_mat_nrows(mat); i++) {
    flint_fprintf(file, "[");
    
    for (j = 0; j < arb_mat_ncols(mat); j++) {
      arb_fprintn(file, arb_mat_entry(mat, i, j), digits, options);
      
      if (j < arb_mat_ncols(mat) - 1) flint_fprintf(file, ", ");
    }
    
    flint_fprintf(file, "]\n");
  }
}
