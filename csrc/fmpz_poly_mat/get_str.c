#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include <flint/flint.h>
#include <flint/fmpz.h>
#include <flint/fmpz_poly_mat.h>

#include "../fmpz_poly_mat.h"

char*
fmpz_poly_mat_get_str(const fmpz_poly_mat_t mat, const char * x)
{
   char * buffer = NULL;
   size_t buffer_size = 0;

   FILE * out = open_memstream(&buffer, &buffer_size);

   fmpz_poly_mat_fprint(out, mat, x);

   fclose(out);

   return buffer;
}
