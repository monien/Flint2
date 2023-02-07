#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include <flint/flint.h>
#include <flint/padic.h>
#include <flint/padic_mat.h>

#include "../padic_mat.h"

char*
padic_mat_get_str(const padic_mat_t mat)
{
   char * buffer = NULL;
   size_t buffer_size = 0;

   FILE * out = open_memstream(&buffer, &buffer_size);

   padic_mat_fprint(out, mat);

   fclose(out);

   return buffer;
}
