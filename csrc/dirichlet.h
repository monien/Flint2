#ifndef CSRC_DIRICHLET_H_
#define CSRC_DIRICHLET_H_

#include <stdlib.h>
#include <flint/dirichlet.h>

void
dirichlet_char_fprint(FILE *file,
		      const dirichlet_group_t G,
		      const dirichlet_char_t x);

char*
dirichlet_char_get_str(const dirichlet_group_t G,
		       const dirichlet_char_t x);

#endif // CSRC_DIRICHLET_H_
