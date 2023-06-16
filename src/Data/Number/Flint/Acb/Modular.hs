{- |
This module provides methods for numerical evaluation of modular forms
and Jacobi theta functions. See module [Data.Number.Flint.Acb.Elliptic]("Data.Number.Flint.Acb.Elliptic") for the closely related elliptic functions and integrals.

In the context of this module, /tau/ or \(\tau\) always denotes an
element of the complex 
upper half-plane \(\mathbb{H} = \{z\in\mathbb{C}:\operatorname{Im}(z) > 0\}\). 
We also often use the variable \(q\),
variously defined as \(q = e^{2 \pi i \tau}\) (usually in relation to
modular forms) or \(q = e^{\pi i \tau}\) (usually in relation to theta
functions) and satisfying \(|q| < 1\). We will clarify the local meaning
of \(q\) every time such a quantity appears as a function of \(\tau\).

As usual, the numerical functions in this module compute strict error
bounds: if /tau/ is represented by an "Acb" whose content overlaps
with the real line (or lies in the lower half-plane), and /tau/ is
passed to a function defined only on \(\mathbb{H}\), then the output
will have an infinite radius. The analogous behavior holds for functions
requiring \(|q| < 1\).
-}

module Data.Number.Flint.Acb.Modular (
  module Data.Number.Flint.Acb.Modular.FFI
  ) where

import Data.Number.Flint.Acb.Modular.FFI