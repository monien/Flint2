#include <stdlib.h>
#include <flint/perm.h>

#include "../perm.h"

void _perm_power(slong *x_p, slong *x, slong p, slong n) {

  ulong tmp = labs(p);

  slong *w = _perm_init(n);

  _perm_set(x_p, w, n);
  _perm_set(w, x, n);

  for(slong j=0; j<8*sizeof(ulong); j++) {
    if( tmp & 0x1 ) {
      _perm_compose(x_p, x_p, w, n);
    }
    _perm_compose(w, w, w, n);
    tmp >>= 1;
  }

  if( p < 0 ) _perm_inv(x_p, x_p, n);
  
  _perm_clear(w);
}
