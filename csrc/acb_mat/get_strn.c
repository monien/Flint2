#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include <flint/flint.h>
#include <flint/acb.h>
#include <flint/acb_mat.h>

#include "../acb_mat.h"

char*
acb_mat_get_strn(const acb_mat_t mat, slong digits, ulong options)
{
   char * buffer = NULL;
   size_t buffer_size = 0;

   FILE * out = open_memstream(&buffer, &buffer_size);

   acb_mat_fprintn(out, mat, digits, options);

   fclose(out);

   return buffer;
}
