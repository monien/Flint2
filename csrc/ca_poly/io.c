/*
    Copyright (C) 2020 Fredrik Johansson

    This file is part of Calcium.

    Calcium is free software: you can redistribute it and/or modify it under
    the terms of the GNU Lesser General Public License (LGPL) as published
    by the Free Software Foundation; either version 2.1 of the License, or
    (at your option) any later version.  See <http://www.gnu.org/licenses/>.
*/

#include "ca_poly.h"

void
ca_poly_fprint(FILE *file, const ca_poly_t poly, ca_ctx_t ctx)
{
    slong i, len;

    len = poly->length;

    flint_fprintf(file, "ca_poly of length %wd:\n", len);

    for (i = 0; i < len; i++)
    {
      char *str = ca_get_str(poly->coeffs + i, ctx);
      flint_fprintf(file, "    %s\n", str);
      flint_free(str);
    }

    flint_fprintf(file, "\n");
}

char*
ca_poly_get_str(const ca_poly_t poly, ca_ctx_t ctx)
{
   char * buffer = NULL;
   size_t buffer_size = 0;

   FILE * out = open_memstream(&buffer, &buffer_size);

   ca_poly_fprint(out, poly, ctx);

   fclose(out);

   return buffer;
}
