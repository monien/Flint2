#include <flint/fmpz.h>
#include <flint/fmpq.h>
#include <flint/fmpq_poly.h>

#include "../fmpq_poly.h"

void
_fmpq_poly_monien_h (fmpz * coeffs, fmpz_t den, ulong n)
{
  fmpz_t c;
  int odd;
  ulong k;
  ulong L;

  if (n == 0)
    {
      fmpz_one (coeffs);
      fmpz_one (den);
      return;
    }

  if (n == 1)
    {
      fmpz_zero (coeffs);
      fmpz_set_si(coeffs, -1);
      fmpz_set_ui(coeffs + 1, 15);
      fmpz_set_ui(den, 15);
      return;
    }

  fmpz_init (c);

  for (k = 0; k <= n; k++)
    {
      fmpz_fac_ui (coeffs + k, 2 * (n + k) + 1);
      fmpz_fac_ui (c, 2 * (n - k) + 1);
      fmpz_divexact (coeffs + k, coeffs + k, c);
      fmpz_fac_ui (c, 2 * k);
      fmpz_divexact (coeffs + k, coeffs + k, c);
      fmpz_set_si (c, -4);
      fmpz_pow_ui (c, c, k);
      fmpz_divexact (coeffs + k, coeffs + k, c);
    }

  fmpz_fac_ui (den, 4 * n + 1);
  fmpz_fac_ui (c, 2 * n);
  fmpz_divexact (den, den, c);
  fmpz_set_si (c, -4);
  fmpz_pow_ui (c, c, n);
  fmpz_divexact (den, den, c);

  fmpz_clear (c);

}

void
fmpq_poly_monien_h (fmpq_poly_t poly, ulong n)
{
  fmpq_poly_fit_length (poly, n + 1);
  _fmpq_poly_monien_h (poly->coeffs, poly->den, n);
  _fmpq_poly_set_length (poly, n + 1);
}
