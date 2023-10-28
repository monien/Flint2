{-|
module      :  Data.Number.Flint.Arb.Types.FFI
copyright   :  (c) 2022 Hartmut Monien
license     :  GNU GPL, version 2 or above (see LICENSE)
maintainer  :  hmonien@uni-bonn.de
-}
module Data.Number.Flint.Arb.Types.FFI where

import Foreign.C.String
import Foreign.C.Types
import Foreign.ForeignPtr
import Foreign.Ptr ( Ptr, FunPtr, nullPtr, plusPtr )
import Foreign.Storable
import Foreign.Marshal ( free )
import Foreign.Marshal.Array ( advancePtr )

import Data.Number.Flint.Flint.Internal
import Data.Number.Flint.Flint.External
import Data.Number.Flint.Fmpz

#include <flint/arf.h>
#include <flint/mag.h>
#include <flint/arb.h>

-- mag_t -----------------------------------------------------------------------

-- | Data structure containing the CMag pointer
data Mag = Mag {-# UNPACK #-} !(ForeignPtr CMag)
data CMag = CMag CFmpz CMpLimb

instance Storable CMag where
  sizeOf _ = #{size mag_t}
  alignment _ = #{alignment mag_t}
  peek ptr = CMag
    <$> #{peek mag_struct, exp} ptr
    <*> #{peek mag_struct, man} ptr
  poke = undefined

-- arf_t -----------------------------------------------------------------------

-- | Data structure containing the CArb pointer
data Arf = Arf {-# UNPACK #-} !(ForeignPtr CArf) 
data CArf = CFlint CArf 

instance Storable CArf where
  sizeOf    _ = #{size      arf_t}
  alignment _ = #{alignment arf_t}
  peek = error "CArf.peek undefined."
  poke = error "CArf.poke undefined."

-- >>> Arf depends on a c-union which cannot be converted to a Haskell type

-- | Arf rounding
newtype ArfRnd = ArfRnd {_ArfRnd :: CInt}
  deriving (Show, Eq)

-- | Specifies that the result of an operation should be rounded to
-- the nearest representable number in the direction towards zero.
arf_rnd_up    = ArfRnd #const ARF_RND_UP
-- | Specifies that the result of an operation should be rounded to
-- the nearest representable number in the direction away from zero.
arf_rnd_down  = ArfRnd #const ARF_RND_DOWN
-- | Specifies that the result of an operation should be rounded to
-- the nearest representable number in the direction towards minus
-- infinity.
arf_rnd_floor = ArfRnd #const ARF_RND_FLOOR
-- | Specifies that the result of an operation should be rounded to
-- the nearest representable number in the direction towards plus
-- infinity.
arf_rnd_ceil  = ArfRnd #const ARF_RND_CEIL
-- | Specifies that the result of an operation should be rounded to
-- the nearest representable number, rounding to even if there is a
-- tie between two values.
arf_rnd_near  = ArfRnd #const ARF_RND_NEAR
-- | If passed as the precision parameter to a function, indicates
-- that no rounding is to be performed. __Warning__: use of this value
-- is unsafe in general. It must only be passed as input under the
-- following two conditions:
-- 
--  * The operation in question can inherently be viewed as an exact operation
--    in \(\mathbb{Z}[\tfrac{1}{2}]\) for all possible inputs, provided that
--    the precision is large enough. Examples include addition,
--    multiplication, conversion from integer types to arbitrary-precision
--    floating-point types, and evaluation of some integer-valued functions.
--
--  * The exact result of the operation will certainly fit in memory.
--    Note that, for example, adding two numbers whose exponents are far
--    apart can easily produce an exact result that is far too large to
--    store in memory.
--
--  The typical use case is to work with small integer values, double
--  precision constants, and the like. It is also useful when writing
--  test code. If in doubt, simply try with some convenient high precision
--  instead of using this special value, and check that the result is exact.
arf_prec_exact = ArfRnd #const ARF_PREC_EXACT

-- arb_t -----------------------------------------------------------------------

-- | Data structure containing the CArb pointer
data Arb = Arb {-# UNPACK #-} !(ForeignPtr CArb) 
data CArb = CArb CMag CArf

instance Storable CArb where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size arb_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment arb_t}
  peek = error "CArb.peek undefined."
  poke = error "CArb.poke undefined."
  
-- | string options
newtype ArbStrOption = ArbStrOption {_ArbStrOption :: CULong}
  deriving (Show, Eq)

instance Num ArbStrOption where
  (+) (ArbStrOption x) (ArbStrOption y) = ArbStrOption (x + y)
  (*) = undefined
  abs = undefined
  signum = error "ArbStrOption: \"signum\" not defined."
  fromInteger = error "ArbStrOption: \"fromInteger\" not defined."
  negate = error "ArbStrOption: \"negate\" not defined."

-- | Default print option
arb_str_none      = ArbStrOption 0
-- | If /arb_str_more/ is added to flags, more (possibly incorrect)
-- digits may be printed
arb_str_more      = ArbStrOption #const ARB_STR_MORE
-- | If /arb_str_no_radius/ is added to /flags/, the radius is not
-- included in the output if at least 1 digit of the midpoint can be
-- printed.
arb_str_no_radius = ArbStrOption #const ARB_STR_NO_RADIUS
-- | By adding a multiple m of /arb_str_condense/ to /flags/, strings of
-- more than three times m consecutive digits are condensed, only
-- printing the leading and trailing m digits along with brackets
-- indicating the number of digits omitted (useful when computing
-- values to extremely high precision).
arb_str_condense  = ArbStrOption #const ARB_STR_CONDENSE

-- arb_poly_t ------------------------------------------------------------------

-- | Data structure containing the CArb pointer
data ArbPoly = ArbPoly {-# UNPACK #-} !(ForeignPtr CArbPoly) 
type CArbPoly = CFlint ArbPoly
