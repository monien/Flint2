#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include <flint/flint.h>
#include <flint/fmpz.h>
#include <flint/fmpz_mat.h>

#include "../fmpz_mat.h"

char*
fmpz_mat_get_str_pretty(const fmpz_mat_t mat)
{
   char * buffer = NULL;
   size_t buffer_size = 0;

   FILE * out = open_memstream(&buffer, &buffer_size);

   fmpz_mat_fprint_pretty(out, mat);

   fclose(out);

   return buffer;
}
