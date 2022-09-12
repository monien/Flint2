#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include <flint/flint.h>
#include <flint/fmpz.h>
#include <flint/fmpz_factor.h>

#include "../fmpz_factor.h"

void
fmpz_factor_fprint(FILE * out, const fmpz_factor_t factor)
{
    slong i;

    if (factor->sign == 0)
    {
        flint_fprintf(out, "0");
        return;
    }

    if (factor->sign == -1)
    {
        if (factor->num)
	    flint_fprintf(out, "-1 * ");
        else
	    flint_fprintf(out, "-1");
    }

    for (i = 0; i < factor->num; i++)
    {
      fmpz_fprint(out, factor->p + i);

        if (factor->exp[i] != UWORD(1))
	  flint_fprintf(out, "^%wu", factor->exp[i]);

        if (i != factor->num - 1)
	  flint_fprintf(out, " * ");
    }
}
