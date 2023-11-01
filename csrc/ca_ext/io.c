/*
  Copyright (C) 2020 Fredrik Johansson

  This file is part of Calcium.

  Calcium is free software: you can redistribute it and/or modify it under
  the terms of the GNU Lesser General Public License (LGPL) as published
  by the Free Software Foundation; either version 2.1 of the License, or
  (at your option) any later version.  See <http://www.gnu.org/licenses/>.
*/

#include <stdio.h>
#include <flint/flint.h>
#include <flint/ca_ext.h>

#include "../qqbar.h"
#include "../ca_ext.h"

void
ca_ext_fprint(FILE *file, const ca_ext_t x, ca_ctx_t ctx)
{
  if (x->head == CA_QQBar)
    {
      flint_fprintf(file, "Algebraic ");

      if (qqbar_is_i(CA_EXT_QQBAR(x)))
	flint_fprintf(file, "I");
      else
        {
	  /*
            flint_fprintf(file, "Algebraic [deg %wd] ", qqbar_degree(CA_EXT_QQBAR(x)));
            qqbar_printn(CA_EXT_QQBAR(x), 10);
	  */

	  qqbar_fprintn(file, CA_EXT_QQBAR(x), 8);
	  /*
            flint_fprintf(file, " (");
            fmpz_poly_print_pretty(QQBAR_POLY(CA_EXT_QQBAR(x)), "a");
            flint_fprintf(file, "=0)");
	  */
        }
    }
  else
    {
      flint_fprintf(file, "%s", calcium_func_name(CA_EXT_HEAD(x)));

      if (CA_EXT_FUNC_NARGS(x) != 0)
        {
	  slong i;
	  flint_fprintf(file, "(");
	  for (i = 0; i < CA_EXT_FUNC_NARGS(x); i++)
            {
	      ca_fprint(file, CA_EXT_FUNC_ARGS(x) + i, ctx);

	      if (i < CA_EXT_FUNC_NARGS(x) - 1)
		flint_fprintf(file, ", ");
            }
	  flint_fprintf(file, ")");
        }
    }
}

char*
ca_ext_get_str(const ca_ext_t x, ca_ctx_t ctx)
{
   char * buffer = NULL;
   size_t buffer_size = 0;

   FILE * out = open_memstream(&buffer, &buffer_size);

   ca_ext_fprint(out, x, ctx);

   fclose(out);

   return buffer;
}
