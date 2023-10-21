#include <stdio.h>
#include <flint/fmpz_mpoly_factor.h>


void
fmpz_mpoly_factor_fprint_pretty(FILE *file,
				const fmpz_mpoly_factor_t f,
                                const char ** vars,
				const fmpz_mpoly_ctx_t ctx) {
  slong i;
  
  fmpz_fprint(file, f->constant);
  for (i = 0; i < f->num; i++) {
    flint_fprintf(file, "*(", i);
    fmpz_mpoly_fprint_pretty(file, f->poly + i, vars, ctx);
    flint_fprintf(file, ")^");
    fmpz_fprint(file, f->exp + i);
  }

  
}

char*
fmpz_mpoly_factor_get_str_pretty(const fmpz_mpoly_factor_t f,
				 const char ** vars,
				 const fmpz_mpoly_ctx_t ctx) {
   char * buffer = NULL;
   size_t buffer_size = 0;

   FILE * out = open_memstream(&buffer, &buffer_size);

   fmpz_mpoly_factor_fprint_pretty(out, f, vars, ctx);

   fclose(out);

   return buffer;
}

