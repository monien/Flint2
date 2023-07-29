#include <stdio.h>
#include <stdlib.h>

#include <flint/flint.h>
#include <flint/fmpq.h>
#include <flint/fmpq_poly.h>

int
fmpq_poly_fprint_pretty_as_series(
  FILE *file,
  fmpq_poly_t poly,
  const char *var
) {

  fmpq_t c;
  
  fmpq_init(c);

  slong k = 0;
  
  if(poly->length == 0) {
    flint_fprintf(file, "0");
    return 0;
  }

  while( fmpz_is_zero(poly->coeffs+k) ) {
    k++;
  }
  
  for(slong j=k; j<poly->length; j++) {
    if( fmpz_is_zero(poly->coeffs+j) ) continue;
    fmpq_set_fmpz_frac(c, poly->coeffs+j, poly->den);
    if( j > k ) {
      if( fmpq_cmp_si(c, 0) > 0 ) {
	flint_fprintf(file, " + ");
      } else {
	flint_fprintf(file, " - ");
      }
    } else {
      if( fmpq_cmp_si(c, 0) < 0 ) {
	flint_fprintf(file, "-");
      }
    }
    if( fmpq_is_pm1(c) ) {
      if( j > 0) {
	if( j > 1 ) {
	  flint_fprintf(file, "%s^%d", var, j);
	} else {
	  flint_fprintf(file, "%s", var);
	}
      }
    } else {
      fmpq_abs(c, c);
      fmpq_fprint(file, c);
      if( j > 1 ) {
	flint_fprintf(file, "*%s^%d", var, j);
      } else {
	flint_fprintf(file, "*%s", var);
      }
    }
  }

  flint_fprintf(file, " + O(%s^%d)", var, poly->length);

  return 0;
}
   
char * fmpq_poly_get_str_pretty_as_series(fmpq_poly_t poly, const char *var) {
  char * buffer = NULL;
  size_t buffer_size = 0;
  FILE * out = open_memstream(&buffer, &buffer_size);
  fmpq_poly_fprint_pretty_as_series(out, poly, var);
  fclose(out);
  return buffer;
}

int fmpq_poly_print_pretty_as_series(fmpq_poly_t poly, const char *var) {
  return fmpq_poly_fprint_pretty_as_series(stdout, poly, var);
}
