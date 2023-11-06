/*
  Copyright (C) 2022 Hartmut Monien

  This file is part of Arb.

  Arb is free software: you can redistribute it and/or modify it under
  the terms of the GNU Lesser General Public License (LGPL) as published
  by the Free Software Foundation; either version 2.1 of the License, or
  (at your option) any later version.  See <http://www.gnu.org/licenses/>.
*/

#include <stdlib.h>
#include <flint/dirichlet.h>

#include "dirichlet.h"

void
dirichlet_char_fprint(FILE *file,
		      const dirichlet_group_t G,
		      const dirichlet_char_t x)
{
  slong k;
  if (G->num)
    flint_fprintf(file, "[%wu", x->log[0]);
  else
    flint_printf("[");
  for (k = 1; k < G->num; k++)
    flint_fprintf(file, ", %wu", x->log[k]);
  flint_fprintf(file, "]");
}

char*
dirichlet_char_get_str(const dirichlet_group_t G,
		       const dirichlet_char_t x)
{
   char * buffer = NULL;
   size_t buffer_size = 0;

   FILE * out = open_memstream(&buffer, &buffer_size);

   dirichlet_char_fprint(out, G, x);

   fclose(out);

   return buffer;
}

