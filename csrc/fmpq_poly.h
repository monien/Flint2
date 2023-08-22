#ifndef CSRC_FMPQ_POLY_H_
#define CSRC_FMPQ_POLY_H_

#include <stdio.h>
#include <flint/fmpq_poly.h>

void
fmpq_poly_fprint_pretty_as_series(
  FILE *file,
  fmpq_poly_t poly,
  const char *var
);

char * fmpq_poly_get_str_pretty_as_series(fmpq_poly_t poly, const char *var);
void fmpq_poly_print_pretty_as_series(fmpq_poly_t poly, const char *var);

void _fmpq_poly_monien_h (fmpz * coeffs, fmpz_t den, ulong n);
void fmpq_poly_monien_h (fmpq_poly_t poly, ulong n);

#endif // CSRC_FMPQ_POLY_H_
