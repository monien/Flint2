module Data.Number.Flint.Arb.Types.FFI where

import Foreign.C.String
import Foreign.C.Types
import Foreign.ForeignPtr
import Foreign.Ptr ( Ptr, FunPtr, nullPtr, plusPtr )
import Foreign.Storable
import Foreign.Marshal ( free )
import Foreign.Marshal.Array ( advancePtr )

#include <flint/arf.h>
#include <flint/arb.h>

-- | Data structure containing the CMag pointer
data Mag = Mag {-# UNPACK #-} !(ForeignPtr CMag)
data CMag = CMag

-- arf_t -----------------------------------------------------------------------

-- | Data structure containing the CArb pointer
data Arf = Arf {-# UNPACK #-} !(ForeignPtr CArf) 
data CArf = CArf

-- | Arf rounding
newtype ArfRnd = ArfRnd {_ArfRnd :: CInt}
  deriving (Show, Eq)

arf_rnd_near   = ArfRnd #const ARF_RND_NEAR
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
data CArb = CArb

-- | string options
newtype ArbStrOption = ArbStrOption {_ArbStrOption :: CULong}
  deriving (Show, Eq)

instance Num ArbStrOption where
  (+) (ArbStrOption x) (ArbStrOption y) = ArbStrOption (x + y)
  (*) = undefined
  abs = undefined
  signum = undefined
  fromInteger = undefined
  negate = undefined

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
