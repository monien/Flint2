#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include <flint/flint.h>
#include <flint/fq_zech.h>
#include <flint/fq_zech_mat.h>

#include "../fq_zech_mat.h"

char*
fq_zech_mat_get_str_pretty(const fq_zech_mat_t mat, fq_zech_ctx_t ctx)
{
   char * buffer = NULL;
   size_t buffer_size = 0;

   FILE * out = open_memstream(&buffer, &buffer_size);

   fq_zech_mat_fprint_pretty(out, mat, ctx);

   fclose(out);

   return buffer;
}
