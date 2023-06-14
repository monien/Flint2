#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include <flint/flint.h>

#include "../qqbar.h"

char*
qqbar_get_strn(const qqbar_t x, slong digits)
{
  char * buffer = NULL;
  size_t buffer_size = 0;
  
  FILE * out = open_memstream(&buffer, &buffer_size);
  
  qqbar_fprintn(out, x, digits);
  
  fclose(out);
  
  return buffer;
}

char*
qqbar_get_strnd(const qqbar_t x, slong digits)
{
  char * buffer = NULL;
  size_t buffer_size = 0;
  
  FILE * out = open_memstream(&buffer, &buffer_size);
  
  qqbar_fprintnd(out, x, digits);
  
  fclose(out);
  
  return buffer;
}
