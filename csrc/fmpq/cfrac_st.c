#include <flint/flint.h>
#include <flint/fmpz.h>
#include <flint/fmpq.h>

#include "../fmpq.h"

slong fmpq_get_cfrac_st(fmpz *c, fmpq_t rem, const fmpq_t x, slong n) {

  slong k = 0;
  fmpq_t y;

  fmpq_init(y);
  fmpq_set(y, x);
  
  fmpz_t q, r;

  fmpz_init(q);
  fmpz_init(r);

  for(slong j=0; j<n; j++) {
    k++;
    fmpz_tdiv_qr(q, r, fmpq_numref(y), fmpq_denref(y));
    if( !fmpz_is_zero(r) ) {
      fmpz_add_ui(c + j, q, 1);
    } else {
      fmpz_set(c + j, q);
    }
    fmpq_set_fmpz_frac(y, r, fmpq_denref(y));
    fmpq_neg(y, y);
    fmpq_add_ui(y, y, 1);
    fmpq_inv(y, y);
    if( fmpz_is_zero(r) ) break;
  };

  fmpq_set(rem, y);
  fmpq_clear(y);
  
  fmpz_clear(q);
  fmpz_clear(r);

  return k;
}

void fmpq_set_cfrac_st(fmpq_t x, const fmpz *c, slong n) {

  fmpq_zero(x);
  
  for(slong j=n-1; j>0; j--) {
    fmpq_add_fmpz(x, x, c + j);
    fmpq_inv(x, x);
    fmpq_neg(x, x);
  }

  fmpq_add_fmpz(x, x, c);
  
}
      
    
  
