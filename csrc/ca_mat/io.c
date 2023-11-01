#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include <stdio.h>
#include <flint/flint.h>
#include <flint/ca.h>
#include <flint/ca_mat.h>

#include "../ca_mat.h"

char*
ca_mat_get_str(const ca_mat_t mat, ca_ctx_t ctx)
{
  char * buffer = NULL;
  size_t buffer_size = 0;

  FILE * out = open_memstream(&buffer, &buffer_size);

  ca_mat_fprint(out, mat, ctx);

  fclose(out);

  return buffer;
}

void
ca_mat_fprint(FILE *file, const ca_mat_t mat, ca_ctx_t ctx)
{
  slong r, c;
  slong i, j;

  r = ca_mat_nrows(mat);
  c = ca_mat_ncols(mat);

  flint_fprintf(file, "ca_mat of size %wd x %wd:\n", r, c);

  for (i = 0; i < r; i++)
    {
      for (j = 0; j < c; j++)
        {
	  flint_fprintf(file, "    ");
	  ca_fprint(file, ca_mat_entry(mat, i, j), ctx);
	  flint_fprintf(file, "\n");
        }

    }

  flint_fprintf(file, "\n");
}
