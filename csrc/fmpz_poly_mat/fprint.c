/*
    Copyright (C) 2011 Fredrik Johansson

    This file is part of FLINT.

    FLINT is free software: you can redistribute it and/or modify it under
    the terms of the GNU Lesser General Public License (LGPL) as published
    by the Free Software Foundation; either version 2.1 of the License, or
    (at your option) any later version.  See <https://www.gnu.org/licenses/>.
*/

#include <stdio.h>

#include <flint/flint.h>
#include <flint/fmpz_poly.h>
#include <flint/fmpz_poly_mat.h>

#include "../fmpz_poly_mat.h"

void
fmpz_poly_mat_fprint(FILE * file, const fmpz_poly_mat_t A, const char * x)
{
  slong i, j;
  
  flint_fprintf(file, "<%wd x %wd matrix over Z[%s]>\n", A->r, A->c, x);

  for (i = 0; i < A->r; i++)
    {
      flint_fprintf(file, "[");
      for (j = 0; j < A->c; j++)
        {
	  fmpz_poly_fprint_pretty(file, fmpz_poly_mat_entry(A, i, j), x);
	  if (j + 1 < A->c)
	    flint_fprintf(file, ", ");
        }
      flint_fprintf(file, "]\n");
    }
  flint_fprintf(file, "\n");
}
