#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include <flint/flint.h>
#include <flint/fmpz.h>
#include <flint/fmpz_mpoly_q.h>

#include "../fmpz_mpoly_q.h"

char*
fmpz_mpoly_q_get_str_pretty(const fmpz_mpoly_q_t x, const char ** vars, const fmpz_mpoly_ctx_t ctx)
{
   char * buffer = NULL;
   size_t buffer_size = 0;

   FILE * out = open_memstream(&buffer, &buffer_size);

   fmpz_mpoly_q_fprint_pretty(out, x, vars, ctx);

   fclose(out);

   return buffer;
}
