#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include <flint/flint.h>
#include <flint/fmpq.h>
#include <flint/fmpq_vec.h>

#include "../fmpq_vec.h"

char*
_fmpq_vec_get_str(const long n, const fmpq_t vec)
{
   char * buffer = NULL;
   size_t buffer_size = 0;

   FILE * out = open_memstream(&buffer, &buffer_size);

   _fmpq_vec_fprint(out, vec, n);

   fclose(out);

   return buffer;
}
