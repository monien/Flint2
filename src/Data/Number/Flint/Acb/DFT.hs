{- |
__Warning__: the interfaces in this module are experimental and may change
without notice.

All functions support aliasing.

Let /G/ be a finite abelian group, and \(\chi\) a character of /G/. For
any map \(f:G\to\mathbb C\), the discrete fourier 
transform \(\hat f:\hat G\to \mathbb C\) is defined by

\[\hat f(\chi) = \sum_{x\in G}\overline{\chi(x)}f(x)\]

Note that by the inversion formula

\[\widehat{\hat{f}}\left(\chi\right) = \# G \times f\left(\chi^{{}-1}\right)\]

it is straightforward to recover \(f\) from its DFT \(\hat f\).
-}

module Data.Number.Flint.Acb.DFT (
  module Data.Number.Flint.Acb.DFT.FFI
  ) where

import Data.Number.Flint.Acb.DFT.FFI
