/*
    Copyright (C) 2014 Fredrik Johansson

    This file is part of Arb.

    Arb is free software: you can redistribute it and/or modify it under
    the terms of the GNU Lesser General Public License (LGPL) as published
    by the Free Software Foundation; either version 2.1 of the License, or
    (at your option) any later version.  See <http://www.gnu.org/licenses/>.
*/

#include <flint/fmpz.h>
#include <flint/acb_types.h>
#
#include <flint/acb_modular.h>

void
psl2z_init_(psl2z_t g)
{
    fmpz_init(&g->a);
    fmpz_init(&g->b);
    fmpz_init(&g->c);
    fmpz_init(&g->d);
    fmpz_one(&g->a);
    fmpz_one(&g->d);
}

void
psl2z_clear_(psl2z_t g)
{
    fmpz_clear(&g->a);
    fmpz_clear(&g->b);
    fmpz_clear(&g->c);
    fmpz_clear(&g->d);
}

void
psl2z_swap_(psl2z_t f, psl2z_t g)
{
    psl2z_struct h = *f;
    *f = *g;
    *g = h;
}

void
psl2z_set_(psl2z_t h, const psl2z_t g)
{
    fmpz_set(&h->a, &g->a);
    fmpz_set(&h->b, &g->b);
    fmpz_set(&h->c, &g->c);
    fmpz_set(&h->d, &g->d);
}

void
psl2z_one_(psl2z_t g)
{
    fmpz_one(&g->a);
    fmpz_zero(&g->b);
    fmpz_zero(&g->c);
    fmpz_one(&g->d);
}

int
psl2z_equal_(const psl2z_t f, const psl2z_t g)
{
    return fmpz_equal(&f->a, &g->a)
        && fmpz_equal(&f->b, &g->b)
        && fmpz_equal(&f->c, &g->c)
        && fmpz_equal(&f->d, &g->d);
}

int
psl2z_is_one_(const psl2z_t f)
{
  return
    fmpz_is_one(&f->a)
    && fmpz_is_zero(&f->b)
    && fmpz_is_zero(&f->c)
    && fmpz_is_one(&f->d);
}
    
