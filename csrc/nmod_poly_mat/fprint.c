#include <stdio.h>

#include <flint/flint.h>
#include <flint/nmod_poly.h>
#include <flint/nmod_poly_mat.h>

#include "../nmod_poly_mat.h"

void
nmod_poly_mat_fprint(FILE * file, const nmod_poly_mat_t A, const char * x)
{
    slong i, j;

    flint_fprintf(file, "<%wd x %wd matrix over Z/nZ[%s]>\n", A->r, A->c, x);

    for (i = 0; i < A->r; i++)
    {
      flint_fprintf(file, "[");
        for (j = 0; j < A->c; j++)
        {
            /* TODO: pretty */
	  nmod_poly_fprint(file, nmod_poly_mat_entry(A, i, j));
            if (j + 1 < A->c)
	      flint_fprintf(file, ", ");
        }
        flint_fprintf(file, "]\n");
    }
    flint_fprintf(file, "\n");
}
