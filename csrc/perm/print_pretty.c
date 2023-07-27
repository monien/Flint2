#include <stdio.h>

#include "../perm.h"

void cycle_fprint(FILE *file,  slong *x, slong n) {

  slong k = 0;

  if( n > 1 ) {
    
    for(slong j=0; j<n; j++) {
      if( x[j] < x[k] ) k = j;
    }
    
    flint_fprintf(file, "(");
    
    for(slong j=0; j+1<n; j++) {
      flint_fprintf(file, "%d,", x[(j+k) % n] + 1);
    }
  
    flint_fprintf(file, "%d)", x[(n-1+k) % n] + 1);
  }
}

void _perm_fprint_pretty(FILE *file, slong *x, slong n) {

  slong *m = flint_malloc(n * sizeof(slong));
  slong *c = flint_malloc(n * sizeof(slong));
  
  slong k, l, mark = 0;
  
  int found, flag = 1;

  for(slong j=0; j<n; j++) {
    m[j] = j;
    flag = flag && (x[j] == j);
  }
  
  if ( flag ) {
    flint_fprintf(file, "()");
    return;
  }
  
  do {
    found = 0;
    for(slong j=0; j<n; j++) {
      if( m[j] < 0 ) {
      } else {
	// found unmarked
	found = 1;
	mark--;
	l = 0;
	k = j;
	do {
	  m[k] = mark;
	  k = x[k];
	  c[l] = k;;
	  l++;
	} while( m[k] >= 0 );
      }
      cycle_fprint(file, c, l);
      l = 0;
    }
  } while( found );

  flint_free(m);
  flint_free(c);
}

void _perm_print_pretty(slong *x, slong n) {
  _perm_fprint_pretty(stdout, x, n);
}

char * _perm_get_str_pretty(slong *x, slong n) {
  char * buffer = NULL;
  size_t buffer_size = 0;
  FILE * out = open_memstream(&buffer, &buffer_size);
  _perm_fprint_pretty(out, x, n);
  fclose(out);
  return buffer;
}


