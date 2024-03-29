/*
    Copyright (C) 2007 David Howden
    Copyright (C) 2007, 2008, 2009, 2010 William Hart
    Copyright (C) 2008 Richard Howell-Peak
    Copyright (C) 2011 Fredrik Johansson
    Copyright (C) 2023 Hartmut Monien

    This file is part of FLINT.

    FLINT is free software: you can redistribute it and/or modify it under
    the terms of the GNU Lesser General Public License (LGPL) as published
    by the Free Software Foundation; either version 2.1 of the License, or
    (at your option) any later version.  See <https://www.gnu.org/licenses/>.
*/

#include <flint/nmod_poly.h>
#include <flint/nmod_poly_factor.h>

void
nmod_poly_factor_fprint(FILE * file, const nmod_poly_factor_t fac)
{
  slong i;
  
  for (i = 0; i < fac->num; i++)
    {
      nmod_poly_fprint(file, fac->p + i);
      flint_fprintf(file, " ^ %wd\n", fac->exp[i]);
    }
}
