/*
  Copyright (C) 2023 Albin Ahlbäck

  This file is part of FLINT.
  
  FLINT is free software: you can redistribute it and/or modify it under
  the terms of the GNU Lesser General Public License (LGPL) as published
  by the Free Software Foundation; either version 2.1 of the License, or
  (at your option) any later version.  See <https://www.gnu.org/licenses/>.
*/

#include <flint/flint.h>
#include <flint/fmpz.h>
#include <flint/qfb.h>
				       
#include "../qfb.h"
				       
/* printing *******************************************************************/

void qfb_fprint(FILE * out, const qfb_t q)
{
    flint_fprintf(out, "(");
    fmpz_fprint(out, q->a); flint_fprintf(out, ", ");
    fmpz_fprint(out, q->b); flint_fprintf(out, ", ");
    fmpz_fprint(out, q->c); flint_fprintf(out, ")");
}
