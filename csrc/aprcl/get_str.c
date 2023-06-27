#include <flint/fmpz_mod_poly.h>
#include <flint/aprcl.h>

#include "../aprcl.h"

char*
unity_zp_get_str(const unity_zp z)
{
   char * buffer = NULL;
   size_t buffer_size = 0;

   FILE * out = open_memstream(&buffer, &buffer_size);

   unity_zp_fprint(out, z);

   fclose(out);

   return buffer;
}
