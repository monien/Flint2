#include <stdio.h>
#include <flint/acb_modular.h>

char * psl2z_get_str(const psl2z_t x)
{
   char * buffer = NULL;
   size_t buffer_size = 0;

   FILE * out = open_memstream(&buffer, &buffer_size);

   psl2z_fprint(out, x);

   fclose(out);

   return buffer;
}
