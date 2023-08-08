#include <flint/flint.h>
#include <flint/fmpq.h>
#include <flint/fmpz_vec.h>

#include "../fmpq.h"

int main() {
  slong n = 32;
  fmpz *c = _fmpz_vec_init(n);
  const char *s = "5530667668905449271708456552/74748754315003247146347079";
  fmpq_t x, rem;
  fmpq_init(x);
  fmpq_init(rem);
  fmpq_set_str(x, s, 10);
  
  slong m = fmpq_get_cfrac_st(c, rem, x, n);

  _fmpz_vec_print(c, m);
  flint_printf("\n");

  fmpq_t value;
  fmpq_init(value);

  fmpq_set_cfrac_st(value, c, m);

  fmpq_print(value);
  flint_printf("\n");
  
  _fmpz_vec_clear(c, n);
}
