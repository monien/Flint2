#include <stdio.h>
#include <stdlib.h>

#include <flint/flint.h>

#include "../d_mat.h"

void
d_mat_fprint(FILE *file, const d_mat_t mat) {
  slong i, j;  
  flint_fprintf(file, "[");
  for (i = 0; i < mat->r; i++) {
    flint_fprintf(file, "[");
    for (j = 0; j < mat->c; j++) {
      flint_fprintf(file, "%E", d_mat_entry(mat, i, j));
      if (j < mat->c - 1)
	flint_fprintf(file, " ");
    }
    flint_fprintf(file, "]\n");
  }
  flint_fprintf(file, "]\n");
}

char*
d_mat_get_str(const d_mat_t mat) {
  char * buffer = NULL;
  size_t buffer_size = 0;
  FILE * out = open_memstream(&buffer, &buffer_size);
  d_mat_fprint(out, mat);
  fclose(out);
  return buffer;
}
