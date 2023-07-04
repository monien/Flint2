#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include <flint/flint.h>
#include <flint/arb_calc.h>

#include "../arb_calc.h"

char * arf_interval_get_strd(const arf_interval_t u, const slong digits)
{
   char * buffer = NULL;
   size_t buffer_size = 0;

   FILE * out = open_memstream(&buffer, &buffer_size);

   arf_interval_fprintd(out, u, digits);

   fclose(out);

   return buffer;
}
