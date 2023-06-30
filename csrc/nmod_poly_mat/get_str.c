#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include <flint/flint.h>
#include <flint/nmod.h>
#include <flint/nmod_poly_mat.h>

#include "../nmod_poly_mat.h"

char*
nmod_poly_mat_get_str(const nmod_poly_mat_t mat, const char * x)
{
   char * buffer = NULL;
   size_t buffer_size = 0;

   FILE * out = open_memstream(&buffer, &buffer_size);

   nmod_poly_mat_fprint(out, mat, x);

   fclose(out);

   return buffer;
}
