#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include <flint/flint.h>
#include <flint/fmpz.h>
#include <flint/fmpz_vec.h>

#include "../fmpz_vec.h"

char*
_fmpz_vec_get_str(const long n, const fmpz_t vec)
{
   char * buffer = NULL;
   size_t buffer_size = 0;

   FILE * out = open_memstream(&buffer, &buffer_size);

   _fmpz_vec_fprint(out, vec, n);

   fclose(out);

   return buffer;
}
