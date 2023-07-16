#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include <flint/flint.h>
#include <flint/fq.h>

#include "../fq.h"

char*
fq_ctx_get_str(const fq_ctx_t ctx)
{
   char * buffer = NULL;
   size_t buffer_size = 0;

   FILE * out = open_memstream(&buffer, &buffer_size);

   fq_ctx_fprint(out, ctx);

   fclose(out);

   return buffer;
}
