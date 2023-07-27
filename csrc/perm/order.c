#include "../perm.h"

void _perm_order(fmpz_t order, slong *x, slong n) {

  slong *m = _perm_init(n);
  slong k, l, mark = 0;
  
  int found;

  fmpz_t tmp;
  
  fmpz_init(tmp);
  fmpz_set_ui(order, 1);
  
  do {
    found = 0;
    for(slong j=0; j<n; j++) {
      if( m[j] < 0 ) {
      } else {
	// found unmarked
	found = 1;
	mark--;
	k = j;
	l = 0;
	do {
	  m[k] = mark;
	  k = x[k];
	  l++;
	} while ( m[k] >= 0 );
	fmpz_set_si(tmp, l);
	fmpz_lcm(order, order, tmp);
      }
    } 
  } while( found );
  
  fmpz_clear(tmp);
  _perm_clear(m);
}
