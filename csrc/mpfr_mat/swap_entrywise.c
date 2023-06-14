#include <flint/flint.h>
#include <flint/mpfr_mat.h>

#include "../mpfr_mat.h"

void
mpfr_mat_swap_entrywise_(mpfr_mat_t mat1, mpfr_mat_t mat2)
{
    slong i, j;

    for (i = 0; i < mpfr_mat_nrows(mat1); i++)
        for (j = 0; j < mpfr_mat_ncols(mat1); j++)
            mpfr_swap(mpfr_mat_entry(mat2, i, j), mpfr_mat_entry(mat1, i, j));
}
