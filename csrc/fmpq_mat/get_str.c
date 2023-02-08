#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include <flint/flint.h>
#include <flint/fmpq.h>
#include <flint/fmpq_mat.h>

#include "../fmpq_mat.h"

char*
fmpq_mat_get_str(const fmpq_mat_t mat)
{
   char * buffer = NULL;
   size_t buffer_size = 0;

   FILE * out = open_memstream(&buffer, &buffer_size);

   fmpq_mat_fprint(out, mat);

   fclose(out);

   return buffer;
}
