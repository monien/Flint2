#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include <flint/flint.h>
#include <flint/fq_zech.h>

#include "../fmpz_mat.h"

char*
fq_zech_ctx_get_str(const fq_zech_ctx_t ctx)
{
   char * buffer = NULL;
   size_t buffer_size = 0;

   FILE * out = open_memstream(&buffer, &buffer_size);

   fq_zech_ctx_fprint(out, ctx);

   fclose(out);

   return buffer;
}
