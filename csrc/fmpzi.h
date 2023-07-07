#ifndef CSRC_FMPZI_H_
#define CSRC_FMPZI_H_

#include <stdio.h>
#include <flint/fmpzi.h>

void
fmpzi_fprint(FILE * file, const fmpzi_t z);

char*
fmpzi_get_str(const fmpzi_t z);

#endif // CSRC_FMPZI_H_
