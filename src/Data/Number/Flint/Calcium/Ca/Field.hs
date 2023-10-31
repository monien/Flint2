{-|
module      :  Data.Number.Flint.Calcium.Ca.Field
copyright   :  (c) 2023 Hartmut Monien
license     :  GNU GPL, version 2 or above (see LICENSE)
maintainer  :  hmonien@uni-bonn.de

A @CaFieldt@ represents the parent field \(K = \mathbb{Q}(a_1,\ldots,a_n)\)
of a @Ca@ element. A @CaField@ contains a list of pointers to
@CaExt@ objects as well as a reduction ideal.

The user does not normally need to create @CaField@ objects manually:
a @CaCtx@ context object manages a cache of fields automatically.

Internally, three types of field representation are used:

* The trivial field \(\mathbb{Q}\).

* An Antic number field \(\mathbb{Q}(a)\) where \(a\) is defined 
  by a @QQbar@.

* A generic field \(\mathbb{Q}(a_1,\ldots,a_n)\) where \(n \ge 1\),
  and \(a_1\) is not defined by a @QQbar@ if \(n = 1\).

The field type mainly affects the internal storage of the field
elements; the distinction is mostly transparent to the external
interface.

-}
module Data.Number.Flint.Calcium.Ca.Field (
  module Data.Number.Flint.Calcium.Ca.Field.FFI
  ) where
  
import Data.Number.Flint.Calcium.Ca.Field.FFI
