{- |
This module supports computation of elliptic (doubly periodic)
functions, and their inverses, elliptic integrals. See
module [Data.Number.Flint.Acb.Modular]("Data.Number.Flint.Acb.Modular")
for the closely related modular forms and
Jacobi theta functions.

Warning: incomplete elliptic integrals have very complicated branch
structure when extended to complex variables. For some functions in this
module, branch cuts may be artifacts of the evaluation algorithm rather
than having a natural mathematical justification. The user should,
accordingly, watch out for edge cases where the functions implemented
here may differ from other systems or literature. There may also exist
points where a function should be well-defined but the implemented
algorithm fails to produce a finite result due to artificial internal
singularities.
-}

module Data.Number.Flint.Acb.Elliptic (
  module Data.Number.Flint.Acb.Elliptic.FFI
  ) where

import Data.Number.Flint.Acb.Elliptic.FFI
