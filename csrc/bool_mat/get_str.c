#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include <flint/flint.h>
#include <flint/bool_mat.h>

#include "../bool_mat.h"

char*
bool_mat_get_str(const bool_mat_t mat)
{
   char * buffer = NULL;
   size_t buffer_size = 0;

   FILE * out = open_memstream(&buffer, &buffer_size);

   bool_mat_fprint(out, mat);

   fclose(out);

   return buffer;
}
