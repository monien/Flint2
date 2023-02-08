#include "../fmpq_mat.h"

int fmpq_mat_fprint(FILE * file, const fmpq_mat_t mat)
{
  slong i, j;
  
  flint_fprintf(file, "<%wd x %wd matrix over Q>\n", mat->r, mat->c);

  flint_fprintf(file, "[");
  for (i = 0; i < mat->r; i++)
    {
      flint_fprintf(file, "[");
      for (j = 0; j < mat->c; j++)
        {
	  fmpq_fprint(file, fmpq_mat_entry(mat, i, j));
	  if (j + 1 < mat->c)
	    flint_fprintf(file, ", ");
        }
      flint_fprintf(file, "]\n");
    }
  flint_fprintf(file, "]");
  return 1;
}
