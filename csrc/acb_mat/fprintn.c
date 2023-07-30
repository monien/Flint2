#include <flint/acb.h>
#include <flint/acb_mat.h>

#include "../acb_mat.h"

void
acb_mat_fprintn(FILE * file, const acb_mat_t mat, slong digits, ulong options) {
  slong i, j;
  
  for (i = 0; i < acb_mat_nrows(mat); i++) {
    flint_fprintf(file, "[");
    
    for (j = 0; j < acb_mat_ncols(mat); j++) {
      acb_fprintn(file, acb_mat_entry(mat, i, j), digits, options);
      
      if (j < acb_mat_ncols(mat) - 1) flint_fprintf(file, ", ");
    }
    
    flint_fprintf(file, "]\n");
  }
}
