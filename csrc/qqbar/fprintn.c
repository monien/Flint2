/*
    Copyright (C) 2020 Fredrik Johansson

    This file is part of Calcium.

    Calcium is free software: you can redistribute it and/or modify it under
    the terms of the GNU Lesser General Public License (LGPL) as published
    by the Free Software Foundation; either version 2.1 of the License, or
    (at your option) any later version.  See <http://www.gnu.org/licenses/>.
*/

#include <flint/flint.h>
#include <flint/qqbar.h>

#include "../qqbar.h"

void
qqbar_fprintn(FILE * out, const qqbar_t x, slong n)
{
  acb_t t;
  slong prec;
  
  n = FLINT_MAX(1, n);
  prec = n * 3.333 + 10;
  
  acb_init(t);
  qqbar_get_acb(t, x, prec);
  
  acb_fprintn(out, t, n, ARB_STR_NO_RADIUS);
  acb_clear(t);
}

void
qqbar_fprintnd(FILE * out, const qqbar_t x, slong n)
{
  qqbar_fprintn(out, x, n);
  flint_fprintf(out, " (deg %wd)", qqbar_degree(x));
}

