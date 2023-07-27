#include <stdlib.h>
#include <stdio.h>

#include <flint/flint.h>
#include <flint/fmpz.h>
#include <flint/fmpz_vec.h>
#include <flint/acb_modular.h>
#include <flint/perm.h>

#include "../psl2z.h"

void psl2z_word_init(psl2z_word_t word) {
  word->letters = _fmpz_vec_init(1);
  word->alloc = 0;
}

void psl2z_word_clear(psl2z_word_t word) {
  _fmpz_vec_clear(word->letters, word->alloc);
  word->alloc = 0;
}

void psl2z_normal_form(psl2z_t x) {
  if (fmpz_sgn(&x->c) < 0 || (fmpz_is_zero(&x->c) && fmpz_sgn(&x->d) < 0)) {
    fmpz_neg(&x->a, &x->a);
    fmpz_neg(&x->b, &x->b);
    fmpz_neg(&x->c, &x->c);
    fmpz_neg(&x->d, &x->d);
  }
}

void psl2z_get_word(psl2z_word_t word, psl2z_t x) {
  
  if( psl2z_is_one(x) ) return;

  fmpz_t u, v, q, r;

  fmpz_init(u);
  fmpz_init(v);
  fmpz_init(q);
  fmpz_init(r);

  // add space for new letter
  word->alloc += 1;
  if( word->alloc == 1 ) {
    word->letters = flint_malloc(word->alloc * sizeof(fmpz));
  } else {
    word->letters = flint_realloc(word->letters, word->alloc * sizeof(fmpz));
  }
  
  fmpz_init(word->letters + word->alloc - 1);

  // 2*u = 2*(4*a*c + b*d)
  fmpz_mul(u, &x->a, &x->c);
  fmpz_mul_ui(u, u, 4);
  fmpz_mul(r, &x->b, &x->d);
  fmpz_add(u, u, r);
  fmpz_mul_ui(u, u, 2);

  // v = 4*c^2 + d^2
  fmpz_mul(v, &x->c, &x->c);
  fmpz_mul_ui(v, v, 4);
  fmpz_mul(r, &x->d, &x->d);
  fmpz_add(v, v, r);

  // quotRem (2*u + v) (2*v) = (q, r)
  fmpz_add(q, u, v);
  fmpz_mul_ui(r, v, 2);
  fmpz_fdiv_q(q, q, r);
  
  // |2*u| - v
  fmpz_abs(u, u);
  fmpz_sub(u, u, v);

  if( fmpz_cmp_si(u, 0) > 0) {
    // multiply be T ^ (-q)
    fmpz_submul(&x->a, q, &x->c);
    fmpz_submul(&x->b, q, &x->d);
    fmpz_set(word->letters + word->alloc - 1, q);
  } else {
    // multiply by S
    fmpz_swap(&x->a, &x->c);
    fmpz_swap(&x->b, &x->d);
    fmpz_neg(&x->a, &x->a);
    fmpz_neg(&x->b, &x->b);
    fmpz_zero(word->letters + word->alloc - 1);
  }

  psl2z_normal_form(x);

  fmpz_clear(u);
  fmpz_clear(v);
  fmpz_clear(q);
  fmpz_clear(r);

  psl2z_get_word(word, x);
}

void psl2z_set_word(psl2z_t x, psl2z_word_t word) {

  psl2z_one(x);
 
  for(slong j=0; j<word->alloc; j++) {
    fmpz * q = word->letters + word->alloc - 1 - j;
    if( fmpz_cmp_si(q, 0) == 0) {
      // multiply by S
      fmpz_swap(&x->a, &x->c);
      fmpz_swap(&x->b, &x->d);
      fmpz_neg(&x->a, &x->a);
      fmpz_neg(&x->b, &x->b);
    } else {
      // multiply be T ^ q;
      fmpz_addmul(&x->a, q, &x->c);
      fmpz_addmul(&x->b, q, &x->d);
    }
  }

  psl2z_normal_form(x);
}

void _perm_set_word(slong *x, slong *s, slong *t, slong n, psl2z_word_t word) {

  fmpz_t q;
  fmpz_init(q);
  
  slong *r;
  
  _perm_set_one(x, n);
 
  for(slong j=0; j<word->alloc; j++) {
    // fmpz_set(q, word->letters + j);
    fmpz_set(q, word->letters + word->alloc - 1 - j);
    if( fmpz_cmp_si(q, 0) == 0) {
      _perm_compose(x, x, s, n);
    } else {
      // multiply be T ^ q;
      r = _perm_init(n);
      if( fmpz_cmp_si(q, 0) > 0 ) {
	_perm_inv(r, t, n);
	fmpz_neg(q, q);
      } else {
	_perm_set(r, t, n);
      }
      _perm_compose(x, x, r, n);
      _perm_clear(r);
    }
  }

  fmpz_clear(q);

}
 
    
//-- Input and Output ----------------------------------------------------------

void psl2z_word_fprint_pretty(FILE * file, psl2z_word_t word) {
  flint_fprintf(file, "[");
  for(slong j=0; j<word->alloc; j++) {
    flint_fprintf(file, "(");
    if( fmpz_is_zero(word->letters + j) ) {
      flint_fprintf(file, "S,3");
    } else {
      flint_fprintf(file, "T,");
      fmpz_fprint(file, word->letters + j);
    }
    flint_fprintf(file, ")");
    if( j + 1 < word->alloc ) flint_fprintf(file, ",");
  }
  flint_fprintf(file, "]");
}

void psl2z_word_print_pretty(psl2z_word_t word) {
  psl2z_word_fprint_pretty(stdout, word);
}

char * psl2z_word_get_str_pretty(psl2z_word_t word) {
  char * buffer = NULL;
  size_t buffer_size = 0;
  FILE * out = open_memstream(&buffer, &buffer_size);
  psl2z_word_fprint_pretty(out, word);
  fclose(out);
  return buffer;
}

void psl2z_word_fprint(FILE * file, psl2z_word_t word) {
  _fmpz_vec_fprint(file, word->letters, word->alloc);
}

void psl2z_word_print(psl2z_word_t word) {
  psl2z_word_fprint(stdout, word);
}

char * psl2z_word_get_str(psl2z_word_t word) {
  char * buffer = NULL;
  size_t buffer_size = 0;
  FILE * out = open_memstream(&buffer, &buffer_size);
  psl2z_word_fprint(out, word);
  fclose(out);
  return buffer;
}

