/*
    Copyright (C) 2023 Hartmut Monien
    This file is part of Calcium.

    Calcium is free software: you can redistribute it and/or modify it under
    the terms of the GNU Lesser General Public License (LGPL) as published
    by the Free Software Foundation; either version 2.1 of the License, or
    (at your option) any later version.  See <http://www.gnu.org/licenses/>.
*/

#include <stdio.h>
#include "../fmpz_mpoly_q.h"

void
fmpz_mpoly_q_fprint_pretty(FILE *out, const fmpz_mpoly_q_t f, const char ** x, const fmpz_mpoly_ctx_t ctx)
{
    if (fmpz_mpoly_is_one(fmpz_mpoly_q_denref(f), ctx))
    {
      fmpz_mpoly_fprint_pretty(out, fmpz_mpoly_q_numref(f), x, ctx);
    }
    else if (fmpz_mpoly_is_fmpz(fmpz_mpoly_q_denref(f), ctx))
    {
      flint_fprintf(out, "(");
      fmpz_mpoly_fprint_pretty(out, fmpz_mpoly_q_numref(f), x, ctx);
      flint_fprintf(out, ")/");
      fmpz_mpoly_fprint_pretty(out, fmpz_mpoly_q_denref(f), x, ctx);
    }
    else
    {
      flint_fprintf(out, "(");
      fmpz_mpoly_fprint_pretty(out, fmpz_mpoly_q_numref(f), x, ctx);
      flint_fprintf(out, ")/(");
      fmpz_mpoly_fprint_pretty(out, fmpz_mpoly_q_denref(f), x, ctx);
      flint_fprintf(out, ")");
    }
}

