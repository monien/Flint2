#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include <flint/flint.h>
#include <flint/fq_nmod.h>

#include "../fmpz_mat.h"

char*
fq_nmod_ctx_get_str(const fq_nmod_ctx_t ctx)
{
   char * buffer = NULL;
   size_t buffer_size = 0;

   FILE * out = open_memstream(&buffer, &buffer_size);

   fq_nmod_ctx_fprint(out, ctx);

   fclose(out);

   return buffer;
}
