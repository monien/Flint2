{-|
module      :  Data.Number.Flint.Calcium.Ca.Ext
copyright   :  (c) 2023 Hartmut Monien
license     :  GNU GPL, version 2 or above (see LICENSE)
maintainer  :  hmonien@uni-bonn.de


A @CaExt@ represents a fixed real or complex number /a/.

The @CaExt@ structure is heavy-weight object, not just meant to act
as a node in a symbolic expression. It will cache various data to
support repeated computation with this particular number, including its
numerical enclosure and number field data in the case of algebraic
numbers.

Extension numbers are used internally by the @Ca@ type to define the
embeddings \(\mathbb{Q}(a) \to \mathbb{C}\) of formal fields. The user
does not normally need to create @ca_ext_t@ instances directly; the
intended way for the user to work with the extension number /a/ is to
create a @ca_t@ representing the field element \(1 \cdot a\). The
underlying @CaExt@ may be accessed to determine symbolic and
numerical properties of this number.

Since extension numbers may depend recursively on nontrivial fields for
function arguments, @CaExt@ operations require a @CaCtx@ context
object.

-}
module Data.Number.Flint.Calcium.Ca.Ext (
  module Data.Number.Flint.Calcium.Ca.Ext.FFI
  ) where
  
import Data.Number.Flint.Calcium.Ca.Ext.FFI
