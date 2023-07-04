#include <flint/arb_calc.h>

#include "../arb_calc.h"

void
arf_interval_init_(arf_interval_t v)
{
    arf_init(&v->a);
    arf_init(&v->b);
}

void
arf_interval_clear_(arf_interval_t v)
{
    arf_clear(&v->a);
    arf_clear(&v->b);
}

arf_interval_ptr
_arf_interval_vec_init_(slong n)
{
    slong i;
    arf_interval_ptr v =
      (arf_interval_ptr) flint_malloc(sizeof(arf_interval_struct) * n);

    for (i = 0; i < n; i++)
        arf_interval_init(v + i);

    return v;
}

void
_arf_interval_vec_clear_(arf_interval_ptr v, slong n)
{
    slong i;
    for (i = 0; i < n; i++)
        arf_interval_clear(v + i);
    flint_free(v);
}

void
arf_interval_set_(arf_interval_t v, const arf_interval_t u)
{
    arf_set(&v->a, &u->a);
    arf_set(&v->b, &u->b);
}

void
arf_interval_swap_(arf_interval_t v, arf_interval_t u)
{
    arf_swap(&v->a, &u->a);
    arf_swap(&v->b, &u->b);
}

void
arf_interval_get_arb_(arb_t x, const arf_interval_t v, slong prec)
{
    arb_set_interval_arf(x, &v->a, &v->b, prec);
}
