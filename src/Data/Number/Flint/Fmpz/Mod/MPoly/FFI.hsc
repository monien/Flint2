
module Data.Number.Flint.Fmpz.Mod.MPoly.FFI (
  -- * Multivariate polynomials over the integers mod n
    FmpzModMPoly (..)
  , CFmpzModMPoly (..)
  , newFmpzModMPoly
  , withFmpzModMPoly
  -- * Context object
  , FmpzModMPolyCtx (..)
  , CFmpzModMPolyCtx (..)
  , newFmpzModMPolyCtx
  , withFmpzModMPolyCtx
  , fmpz_mod_mpoly_ctx_init
  , fmpz_mod_mpoly_ctx_nvars
  , fmpz_mod_mpoly_ctx_ord
  , fmpz_mod_mpoly_ctx_get_modulus
  , fmpz_mod_mpoly_ctx_clear
  -- * Memory management
  , fmpz_mod_mpoly_init
  , fmpz_mod_mpoly_init2
  , fmpz_mod_mpoly_init3
  , fmpz_mod_mpoly_clear
  -- * Input\/Output
  , fmpz_mod_mpoly_get_str_pretty
  , fmpz_mod_mpoly_fprint_pretty
  , fmpz_mod_mpoly_print_pretty
  , fmpz_mod_mpoly_set_str_pretty
  -- * Basic manipulation
  , fmpz_mod_mpoly_gen
  , fmpz_mod_mpoly_is_gen
  , fmpz_mod_mpoly_set
  , fmpz_mod_mpoly_equal
  , fmpz_mod_mpoly_swap
  -- * Constants
  , fmpz_mod_mpoly_is_fmpz
  , fmpz_mod_mpoly_get_fmpz
  , fmpz_mod_mpoly_set_fmpz
  , fmpz_mod_mpoly_set_ui
  , fmpz_mod_mpoly_set_si
  , fmpz_mod_mpoly_zero
  , fmpz_mod_mpoly_one
  , fmpz_mod_mpoly_equal_fmpz
  , fmpz_mod_mpoly_equal_ui
  , fmpz_mod_mpoly_equal_si
  , fmpz_mod_mpoly_is_zero
  , fmpz_mod_mpoly_is_one
  -- * Degrees
  , fmpz_mod_mpoly_degrees_fit_si
  , fmpz_mod_mpoly_degrees_fmpz
  , fmpz_mod_mpoly_degrees_si
  , fmpz_mod_mpoly_degree_fmpz
  , fmpz_mod_mpoly_degree_si
  , fmpz_mod_mpoly_total_degree_fits_si
  , fmpz_mod_mpoly_total_degree_fmpz
  , fmpz_mod_mpoly_total_degree_si
  , fmpz_mod_mpoly_used_vars
  -- * Coefficients
  , fmpz_mod_mpoly_get_coeff_fmpz_monomial
  , fmpz_mod_mpoly_set_coeff_fmpz_monomial
  , fmpz_mod_mpoly_get_coeff_fmpz_fmpz
  , fmpz_mod_mpoly_get_coeff_fmpz_ui
  , fmpz_mod_mpoly_set_coeff_fmpz_fmpz
  , fmpz_mod_mpoly_set_coeff_ui_fmpz
  , fmpz_mod_mpoly_set_coeff_si_fmpz
  , fmpz_mod_mpoly_set_coeff_fmpz_ui
  , fmpz_mod_mpoly_set_coeff_ui_ui
  , fmpz_mod_mpoly_set_coeff_si_ui
  , fmpz_mod_mpoly_get_coeff_vars_ui
  -- * Comparison
  , fmpz_mod_mpoly_cmp
  -- * Container operations
  , fmpz_mod_mpoly_is_canonical
  , fmpz_mod_mpoly_length
  , fmpz_mod_mpoly_resize
  , fmpz_mod_mpoly_get_term_coeff_fmpz
  , fmpz_mod_mpoly_set_term_coeff_fmpz
  , fmpz_mod_mpoly_set_term_coeff_ui
  , fmpz_mod_mpoly_set_term_coeff_si
  , fmpz_mod_mpoly_term_exp_fits_si
  , fmpz_mod_mpoly_term_exp_fits_ui
  , fmpz_mod_mpoly_get_term_exp_fmpz
  , fmpz_mod_mpoly_get_term_exp_ui
  , fmpz_mod_mpoly_get_term_exp_si
  , fmpz_mod_mpoly_get_term_var_exp_ui
  , fmpz_mod_mpoly_get_term_var_exp_si
  , fmpz_mod_mpoly_set_term_exp_fmpz
  , fmpz_mod_mpoly_set_term_exp_ui
  , fmpz_mod_mpoly_get_term
  , fmpz_mod_mpoly_get_term_monomial
  , fmpz_mod_mpoly_push_term_fmpz_fmpz
  , fmpz_mod_mpoly_push_term_ui_fmpz
  , fmpz_mod_mpoly_push_term_si_fmpz
  , fmpz_mod_mpoly_push_term_fmpz_ui
  , fmpz_mod_mpoly_push_term_ui_ui
  , fmpz_mod_mpoly_push_term_si_ui
  , fmpz_mod_mpoly_sort_terms
  , fmpz_mod_mpoly_combine_like_terms
  -- , fmpz_mod_mpoly_reverse
  -- * Random generation
  , fmpz_mod_mpoly_randtest_bound
  , fmpz_mod_mpoly_randtest_bounds
  , fmpz_mod_mpoly_randtest_bits
  -- * Addition\/Subtraction
  , fmpz_mod_mpoly_add_fmpz
  , fmpz_mod_mpoly_add_ui
  , fmpz_mod_mpoly_add_si
  , fmpz_mod_mpoly_sub_fmpz
  , fmpz_mod_mpoly_sub_ui
  , fmpz_mod_mpoly_sub_si
  , fmpz_mod_mpoly_add
  , fmpz_mod_mpoly_sub
  -- * Scalar operations
  , fmpz_mod_mpoly_neg
  , fmpz_mod_mpoly_scalar_mul_fmpz
  , fmpz_mod_mpoly_scalar_mul_ui
  , fmpz_mod_mpoly_scalar_mul_si
  , fmpz_mod_mpoly_scalar_addmul_fmpz
  , fmpz_mod_mpoly_make_monic
  -- * Differentiation
  , fmpz_mod_mpoly_derivative
  -- * Evaluation
  , fmpz_mod_mpoly_evaluate_all_fmpz
  , fmpz_mod_mpoly_evaluate_one_fmpz
  -- , fmpz_mod_mpoly_compose_fmpz_poly
  , fmpz_mod_mpoly_compose_fmpz_mod_mpoly_geobucket
  , fmpz_mod_mpoly_compose_fmpz_mod_mpoly
  -- , fmpz_mod_mpoly_compose_fmpz_mod_mpoly_gen
  -- * Multiplication
  , fmpz_mod_mpoly_mul
  , fmpz_mod_mpoly_mul_johnson
  , fmpz_mod_mpoly_mul_dense
  -- * Powering
  , fmpz_mod_mpoly_pow_fmpz
  , fmpz_mod_mpoly_pow_ui
  -- * Division
  , fmpz_mod_mpoly_divides
  , fmpz_mod_mpoly_div
  , fmpz_mod_mpoly_divrem
  , fmpz_mod_mpoly_divrem_ideal
  -- * Greatest Common Divisor
  , fmpz_mod_mpoly_term_content
  , fmpz_mod_mpoly_content_vars
  , fmpz_mod_mpoly_gcd
  , fmpz_mod_mpoly_gcd_cofactors
  , fmpz_mod_mpoly_gcd_brown
  , fmpz_mod_mpoly_gcd_hensel
  , fmpz_mod_mpoly_gcd_subresultant
  , fmpz_mod_mpoly_gcd_zippel
  , fmpz_mod_mpoly_gcd_zippel2
  , fmpz_mod_mpoly_resultant
  , fmpz_mod_mpoly_discriminant
  -- * Square Root
  , fmpz_mod_mpoly_sqrt
  , fmpz_mod_mpoly_is_square
  , fmpz_mod_mpoly_quadratic_root
  -- * Univariate Functions
  , fmpz_mod_mpoly_univar_init
  , fmpz_mod_mpoly_univar_clear
  , fmpz_mod_mpoly_univar_swap
  , fmpz_mod_mpoly_to_univar
  , fmpz_mod_mpoly_from_univar
  , fmpz_mod_mpoly_univar_degree_fits_si
  , fmpz_mod_mpoly_univar_length
  , fmpz_mod_mpoly_univar_get_term_exp_si
  , fmpz_mod_mpoly_univar_get_term_coeff
  , fmpz_mod_mpoly_univar_swap_term_coeff
  , fmpz_mod_mpoly_univar_set_coeff_ui
  , fmpz_mod_mpoly_univar_resultant
  , fmpz_mod_mpoly_univar_discriminant
  -- * Internal Functions
  , fmpz_mod_mpoly_inflate
  , fmpz_mod_mpoly_deflate
  , fmpz_mod_mpoly_deflation
) where 

-- Multivariate polynomials over the integers mod n ----------------------------

import Control.Monad

import Foreign.C.String
import Foreign.C.Types
import Foreign.ForeignPtr
import Foreign.Ptr ( Ptr, FunPtr, nullPtr, plusPtr )
import Foreign.Storable
import Foreign.Marshal ( free )
import Foreign.Marshal.Array ( advancePtr )

import Data.Number.Flint.Flint
import Data.Number.Flint.Fmpz
import Data.Number.Flint.Fmpz.Poly
import Data.Number.Flint.Fmpq
import Data.Number.Flint.MPoly
import Data.Number.Flint.Fmpz.Mod

#include <flint/flint.h>
#include <flint/fmpz_mod_mpoly.h>

-- fmpz_mod_mpoly_t ------------------------------------------------------------

data FmpzModMPoly = FmpzModMPoly {-# UNPACK #-} !(ForeignPtr CFmpzModMPoly)
data CFmpzModMPoly = CFmpzModMPoly 

instance Storable CFmpzModMPoly where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size fmpz_mod_mpoly_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment fmpz_mod_mpoly_t}
  peek = error "CFmpzModMPoly.peek: Not defined"
  poke = error "CFmpzModMPoly.poke: Not defined"

-- | Create a new `FmpzModMPoly`
newFmpzModMPoly ctx@(FmpzModMPolyCtx pctx) = do
  p <- mallocForeignPtr
  withForeignPtr p $ \p ->
    withFmpzModMPolyCtx ctx $ \ctx -> do 
      fmpz_mod_mpoly_init p ctx
      addForeignPtrFinalizerEnv p_fmpz_mod_mpoly_clear p pctx 
  return $ FmpzModMPoly p

{-# INLINE withFmpzModMPoly #-}
withFmpzModMPoly (FmpzModMPoly p) f = do
  withForeignPtr p $ \fp -> (FmpzModMPoly p,) <$> f fp

-- fmpz_mod_mpoly_univar_t -----------------------------------------------------

data FmpzModMPolyUnivar = FmpzModMPolyUnivar {-# UNPACK #-} !(ForeignPtr CFmpzModMPolyUnivar)
data CFmpzModMPolyUnivar = CFmpzModMPolyUnivar 

instance Storable CFmpzModMPolyUnivar where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size fmpz_mod_mpoly_univar_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment fmpz_mod_mpoly_univar_t}
  peek = error "CFmpzModMPolyUnivar.peek: Not defined"
  poke = error "CFmpzModMPolyUnivar.poke: Not defined"

-- | Create a new `FmpzModMPolyUnivar`
newFmpzModMPolyUnivar ctx@(FmpzModMPolyCtx pctx) = do
  p <- mallocForeignPtr
  withForeignPtr p $ \p ->
    withFmpzModMPolyCtx ctx $ \ctx -> do 
      fmpz_mod_mpoly_univar_init p ctx
      addForeignPtrFinalizerEnv p_fmpz_mod_mpoly_univar_clear p pctx
  return $ FmpzModMPolyUnivar p

{-# INLINE withFmpzModMPolyUnivar #-}
withFmpzModMPolyUnivar (FmpzModMPolyUnivar p) f = do
  withForeignPtr p $ \fp -> (FmpzModMPolyUnivar p,) <$> f fp
  
-- fmpz_mod_mpoly_ctx_t --------------------------------------------------------

data FmpzModMPolyCtx = FmpzModMPolyCtx {-# UNPACK #-} !(ForeignPtr CFmpzModMPolyCtx)
data CFmpzModMPolyCtx

instance Storable CFmpzModMPolyCtx where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size fmpz_mod_mpoly_ctx_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment fmpz_mod_mpoly_ctx_t}
  peek = error "CFmpzModMPolyCtx.peek: Not defined"
  poke = error "CFmpzModMPolyCtx.poke: Not defined"

-- | Create a new `FmpzModMPolyCtx`
newFmpzModMPolyCtx nvars ord p= do
  x <- mallocForeignPtr
  withForeignPtr x $ \x ->
    fmpz_mod_mpoly_ctx_init x nvars ord p
  addForeignPtrFinalizer p_fmpz_mod_mpoly_ctx_clear x
  return $ FmpzModMPolyCtx x

-- | Use a `FmpzModMPolyCtx`
{-# INLINE withFmpzModMPolyCtx #-}
withFmpzModMPolyCtx (FmpzModMPolyCtx p) f = do
  withForeignPtr p $ \fp -> f fp >>= return . (FmpzModMPolyCtx p,)

-- Context object --------------------------------------------------------------

-- | /fmpz_mod_mpoly_ctx_init/ /ctx/ /nvars/ /ord/ /p/ 
--
-- Initialise a context object for a polynomial ring modulo /n/ with
-- /nvars/ variables and ordering /ord/. The possibilities for the ordering
-- are @ORD_LEX@, @ORD_DEGLEX@ and @ORD_DEGREVLEX@.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_ctx_init"
  fmpz_mod_mpoly_ctx_init :: Ptr CFmpzModMPolyCtx -> CLong -> Ptr COrdering -> Ptr CFmpz -> IO ()

-- | /fmpz_mod_mpoly_ctx_nvars/ /ctx/ 
--
-- Return the number of variables used to initialize the context.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_ctx_nvars"
  fmpz_mod_mpoly_ctx_nvars :: Ptr CFmpzModMPolyCtx -> IO CLong

-- | /fmpz_mod_mpoly_ctx_ord/ /ctx/ 
--
-- Return the ordering used to initialize the context.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_ctx_ord"
  fmpz_mod_mpoly_ctx_ord :: Ptr CFmpzModMPolyCtx -> IO (Ptr COrdering)

-- | /fmpz_mod_mpoly_ctx_get_modulus/ /n/ /ctx/ 
--
-- Set /n/ to the modulus used to initialize the context.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_ctx_get_modulus"
  fmpz_mod_mpoly_ctx_get_modulus :: Ptr CFmpz -> Ptr CFmpzModMPolyCtx -> IO ()

-- | /fmpz_mod_mpoly_ctx_clear/ /ctx/ 
--
-- Release up any space allocated by an /ctx/.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_ctx_clear"
  fmpz_mod_mpoly_ctx_clear :: Ptr CFmpzModMPolyCtx -> IO ()

foreign import ccall "fmpz_mod_mpoly.h &fmpz_mod_mpoly_ctx_clear"
  p_fmpz_mod_mpoly_ctx_clear :: FunPtr (Ptr CFmpzModMPolyCtx -> IO ())

-- Memory management -----------------------------------------------------------

-- | /fmpz_mod_mpoly_init/ /A/ /ctx/ 
--
-- Initialise /A/ for use with the given an initialised context object. Its
-- value is set to zero.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_init"
  fmpz_mod_mpoly_init :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPolyCtx -> IO ()

-- | /fmpz_mod_mpoly_init2/ /A/ /alloc/ /ctx/ 
--
-- Initialise /A/ for use with the given an initialised context object. Its
-- value is set to zero. It is allocated with space for /alloc/ terms and
-- at least @MPOLY_MIN_BITS@ bits for the exponents.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_init2"
  fmpz_mod_mpoly_init2 :: Ptr CFmpzModMPoly -> CLong -> Ptr CFmpzModMPolyCtx -> IO ()

-- | /fmpz_mod_mpoly_init3/ /A/ /alloc/ /bits/ /ctx/ 
--
-- Initialise /A/ for use with the given an initialised context object. Its
-- value is set to zero. It is allocated with space for /alloc/ terms and
-- /bits/ bits for the exponents.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_init3"
  fmpz_mod_mpoly_init3 :: Ptr CFmpzModMPoly -> CLong -> CFBitCnt -> Ptr CFmpzModMPolyCtx -> IO ()

-- | /fmpz_mod_mpoly_clear/ /A/ /ctx/ 
--
-- Release any space allocated for /A/.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_clear"
  fmpz_mod_mpoly_clear :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPolyCtx -> IO ()

foreign import ccall "fmpz_mod_mpoly.h &fmpz_mod_mpoly_clear"
  p_fmpz_mod_mpoly_clear :: FunPtr (Ptr CFmpzModMPoly -> Ptr CFmpzModMPolyCtx -> IO ())

-- Input\/Output ---------------------------------------------------------------

-- | /fmpz_mod_mpoly_get_str_pretty/ /A/ /x/ /ctx/ 
--
-- Return a string, which the user is responsible for cleaning up,
-- representing /A/, given an array of variable strings /x/.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_get_str_pretty"
  fmpz_mod_mpoly_get_str_pretty :: Ptr CFmpzModMPoly -> Ptr (Ptr CChar) -> Ptr CFmpzModMPolyCtx -> IO CString

-- | /fmpz_mod_mpoly_fprint_pretty/ /file/ /A/ /x/ /ctx/ 
--
-- Print a string representing /A/ to /file/.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_fprint_pretty"
  fmpz_mod_mpoly_fprint_pretty :: Ptr CFile -> Ptr CFmpzModMPoly -> Ptr (Ptr CChar) -> Ptr CFmpzModMPolyCtx -> IO CInt

-- | /fmpz_mod_mpoly_print_pretty/ /A/ /x/ /ctx/ 
--
-- Print a string representing /A/ to @stdout@.
fmpz_mod_mpoly_print_pretty :: Ptr CFmpzModMPoly
                            -> Ptr (Ptr CChar)
                            -> Ptr CFmpzModMPolyCtx
                            -> IO CInt
fmpz_mod_mpoly_print_pretty a x ctx = do
  printCStr (\a -> fmpz_mod_mpoly_get_str_pretty a x ctx) a

-- | /fmpz_mod_mpoly_set_str_pretty/ /A/ /str/ /x/ /ctx/ 
--
-- Set /A/ to the polynomial in the null-terminates string /str/ given an
-- array /x/ of variable strings. If parsing /str/ fails, /A/ is set to
-- zero, and \(-1\) is returned. Otherwise, \(0\) is returned. The
-- operations @+@, @-@, @*@, and @\/@ are permitted along with integers and
-- the variables in /x/. The character @^@ must be immediately followed by
-- the (integer) exponent. If any division is not exact, parsing fails.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_set_str_pretty"
  fmpz_mod_mpoly_set_str_pretty :: Ptr CFmpzModMPoly -> CString -> Ptr (Ptr CChar) -> Ptr CFmpzModMPolyCtx -> IO CInt

-- Basic manipulation ----------------------------------------------------------

-- | /fmpz_mod_mpoly_gen/ /A/ /var/ /ctx/ 
--
-- Set /A/ to the variable of index /var/, where \(var = 0\) corresponds to
-- the variable with the most significance with respect to the ordering.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_gen"
  fmpz_mod_mpoly_gen :: Ptr CFmpzModMPoly -> CLong -> Ptr CFmpzModMPolyCtx -> IO ()

-- | /fmpz_mod_mpoly_is_gen/ /A/ /var/ /ctx/ 
--
-- If \(var \ge 0\), return \(1\) if /A/ is equal to the \(var\)-th
-- generator, otherwise return \(0\). If \(var < 0\), return \(1\) if the
-- polynomial is equal to any generator, otherwise return \(0\).
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_is_gen"
  fmpz_mod_mpoly_is_gen :: Ptr CFmpzModMPoly -> CLong -> Ptr CFmpzModMPolyCtx -> IO CInt

-- | /fmpz_mod_mpoly_set/ /A/ /B/ /ctx/ 
--
-- Set /A/ to /B/.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_set"
  fmpz_mod_mpoly_set :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> Ptr CFmpzModMPolyCtx -> IO ()

-- | /fmpz_mod_mpoly_equal/ /A/ /B/ /ctx/ 
--
-- Return \(1\) if /A/ is equal to /B/, else return \(0\).
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_equal"
  fmpz_mod_mpoly_equal :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> Ptr CFmpzModMPolyCtx -> IO CInt

-- | /fmpz_mod_mpoly_swap/ /poly1/ /poly2/ /ctx/ 
--
-- Efficiently swap /A/ and /B/.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_swap"
  fmpz_mod_mpoly_swap :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> Ptr CFmpzModMPolyCtx -> IO ()

-- Constants -------------------------------------------------------------------

-- | /fmpz_mod_mpoly_is_fmpz/ /A/ /ctx/ 
--
-- Return \(1\) if /A/ is a constant, else return \(0\).
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_is_fmpz"
  fmpz_mod_mpoly_is_fmpz :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPolyCtx -> IO CInt

-- | /fmpz_mod_mpoly_get_fmpz/ /c/ /A/ /ctx/ 
--
-- Assuming that /A/ is a constant, set /c/ to this constant. This function
-- throws if /A/ is not a constant.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_get_fmpz"
  fmpz_mod_mpoly_get_fmpz :: Ptr CFmpz -> Ptr CFmpzModMPoly -> Ptr CFmpzModMPolyCtx -> IO ()

-- | /fmpz_mod_mpoly_set_fmpz/ /A/ /c/ /ctx/ 
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_set_fmpz"
  fmpz_mod_mpoly_set_fmpz :: Ptr CFmpzModMPoly -> Ptr CFmpz -> Ptr CFmpzModMPolyCtx -> IO ()
-- | /fmpz_mod_mpoly_set_ui/ /A/ /c/ /ctx/ 
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_set_ui"
  fmpz_mod_mpoly_set_ui :: Ptr CFmpzModMPoly -> CULong -> Ptr CFmpzModMPolyCtx -> IO ()
-- | /fmpz_mod_mpoly_set_si/ /A/ /c/ /ctx/ 
--
-- Set /A/ to the constant /c/.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_set_si"
  fmpz_mod_mpoly_set_si :: Ptr CFmpzModMPoly -> CLong -> Ptr CFmpzModMPolyCtx -> IO ()

-- | /fmpz_mod_mpoly_zero/ /A/ /ctx/ 
--
-- Set /A/ to the constant \(0\).
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_zero"
  fmpz_mod_mpoly_zero :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPolyCtx -> IO ()

-- | /fmpz_mod_mpoly_one/ /A/ /ctx/ 
--
-- Set /A/ to the constant \(1\).
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_one"
  fmpz_mod_mpoly_one :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPolyCtx -> IO ()

-- | /fmpz_mod_mpoly_equal_fmpz/ /A/ /c/ /ctx/ 
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_equal_fmpz"
  fmpz_mod_mpoly_equal_fmpz :: Ptr CFmpzModMPoly -> Ptr CFmpz -> Ptr CFmpzModMPolyCtx -> IO CInt
-- | /fmpz_mod_mpoly_equal_ui/ /A/ /c/ /ctx/ 
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_equal_ui"
  fmpz_mod_mpoly_equal_ui :: Ptr CFmpzModMPoly -> CULong -> Ptr CFmpzModMPolyCtx -> IO CInt
-- | /fmpz_mod_mpoly_equal_si/ /A/ /c/ /ctx/ 
--
-- Return \(1\) if /A/ is equal to the constant /c/, else return \(0\).
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_equal_si"
  fmpz_mod_mpoly_equal_si :: Ptr CFmpzModMPoly -> CLong -> Ptr CFmpzModMPolyCtx -> IO CInt

-- | /fmpz_mod_mpoly_is_zero/ /A/ /ctx/ 
--
-- Return \(1\) if /A/ is the constant \(0\), else return \(0\).
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_is_zero"
  fmpz_mod_mpoly_is_zero :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPolyCtx -> IO CInt

-- | /fmpz_mod_mpoly_is_one/ /A/ /ctx/ 
--
-- Return \(1\) if /A/ is the constant \(1\), else return \(0\).
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_is_one"
  fmpz_mod_mpoly_is_one :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPolyCtx -> IO CInt

-- Degrees ---------------------------------------------------------------------

-- | /fmpz_mod_mpoly_degrees_fit_si/ /A/ /ctx/ 
--
-- Return \(1\) if the degrees of /A/ with respect to each variable fit
-- into an @slong@, otherwise return \(0\).
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_degrees_fit_si"
  fmpz_mod_mpoly_degrees_fit_si :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPolyCtx -> IO CInt

-- | /fmpz_mod_mpoly_degrees_fmpz/ /degs/ /A/ /ctx/ 
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_degrees_fmpz"
  fmpz_mod_mpoly_degrees_fmpz :: Ptr (Ptr CFmpz) -> Ptr CFmpzModMPoly -> Ptr CFmpzModMPolyCtx -> IO ()
-- | /fmpz_mod_mpoly_degrees_si/ /degs/ /A/ /ctx/ 
--
-- Set /degs/ to the degrees of /A/ with respect to each variable. If /A/
-- is zero, all degrees are set to \(-1\).
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_degrees_si"
  fmpz_mod_mpoly_degrees_si :: Ptr CLong -> Ptr CFmpzModMPoly -> Ptr CFmpzModMPolyCtx -> IO ()

-- | /fmpz_mod_mpoly_degree_fmpz/ /deg/ /A/ /var/ /ctx/ 
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_degree_fmpz"
  fmpz_mod_mpoly_degree_fmpz :: Ptr CFmpz -> Ptr CFmpzModMPoly -> CLong -> Ptr CFmpzModMPolyCtx -> IO ()
-- | /fmpz_mod_mpoly_degree_si/ /A/ /var/ /ctx/ 
--
-- Either return or set /deg/ to the degree of /A/ with respect to the
-- variable of index /var/. If /A/ is zero, the degree is defined to be
-- \(-1\).
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_degree_si"
  fmpz_mod_mpoly_degree_si :: Ptr CFmpzModMPoly -> CLong -> Ptr CFmpzModMPolyCtx -> IO CLong

-- | /fmpz_mod_mpoly_total_degree_fits_si/ /A/ /ctx/ 
--
-- Return \(1\) if the total degree of /A/ fits into an @slong@, otherwise
-- return \(0\).
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_total_degree_fits_si"
  fmpz_mod_mpoly_total_degree_fits_si :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPolyCtx -> IO CInt

-- | /fmpz_mod_mpoly_total_degree_fmpz/ /tdeg/ /A/ /ctx/ 
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_total_degree_fmpz"
  fmpz_mod_mpoly_total_degree_fmpz :: Ptr CFmpz -> Ptr CFmpzModMPoly -> Ptr CFmpzModMPolyCtx -> IO ()
-- | /fmpz_mod_mpoly_total_degree_si/ /A/ /ctx/ 
--
-- Either return or set /tdeg/ to the total degree of /A/. If /A/ is zero,
-- the total degree is defined to be \(-1\).
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_total_degree_si"
  fmpz_mod_mpoly_total_degree_si :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPolyCtx -> IO CLong

-- | /fmpz_mod_mpoly_used_vars/ /used/ /A/ /ctx/ 
--
-- For each variable index /i/, set @used[i]@ to nonzero if the variable of
-- index /i/ appears in /A/ and to zero otherwise.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_used_vars"
  fmpz_mod_mpoly_used_vars :: Ptr CInt -> Ptr CFmpzModMPoly -> Ptr CFmpzModMPolyCtx -> IO ()

-- Coefficients ----------------------------------------------------------------

-- | /fmpz_mod_mpoly_get_coeff_fmpz_monomial/ /c/ /A/ /M/ /ctx/ 
--
-- Assuming that /M/ is a monomial, set /c/ to the coefficient of the
-- corresponding monomial in /A/. This function throws if /M/ is not a
-- monomial.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_get_coeff_fmpz_monomial"
  fmpz_mod_mpoly_get_coeff_fmpz_monomial :: Ptr CFmpz -> Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> Ptr CFmpzModMPolyCtx -> IO ()

-- | /fmpz_mod_mpoly_set_coeff_fmpz_monomial/ /A/ /c/ /M/ /ctx/ 
--
-- Assuming that /M/ is a monomial, set the coefficient of the
-- corresponding monomial in /A/ to /c/. This function throws if /M/ is not
-- a monomial.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_set_coeff_fmpz_monomial"
  fmpz_mod_mpoly_set_coeff_fmpz_monomial :: Ptr CFmpzModMPoly -> Ptr CFmpz -> Ptr CFmpzModMPoly -> Ptr CFmpzModMPolyCtx -> IO ()

-- | /fmpz_mod_mpoly_get_coeff_fmpz_fmpz/ /c/ /A/ /exp/ /ctx/ 
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_get_coeff_fmpz_fmpz"
  fmpz_mod_mpoly_get_coeff_fmpz_fmpz :: Ptr CFmpz -> Ptr CFmpzModMPoly -> Ptr (Ptr CFmpz) -> Ptr CFmpzModMPolyCtx -> IO ()
-- | /fmpz_mod_mpoly_get_coeff_fmpz_ui/ /c/ /A/ /exp/ /ctx/ 
--
-- Set /c/ to the coefficient of the monomial with exponent vector /exp/.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_get_coeff_fmpz_ui"
  fmpz_mod_mpoly_get_coeff_fmpz_ui :: Ptr CFmpz -> Ptr CFmpzModMPoly -> Ptr CULong -> Ptr CFmpzModMPolyCtx -> IO ()

-- | /fmpz_mod_mpoly_set_coeff_fmpz_fmpz/ /A/ /c/ /exp/ /ctx/ 
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_set_coeff_fmpz_fmpz"
  fmpz_mod_mpoly_set_coeff_fmpz_fmpz :: Ptr CFmpzModMPoly -> Ptr CFmpz -> Ptr (Ptr CFmpz) -> Ptr CFmpzModMPolyCtx -> IO ()
-- | /fmpz_mod_mpoly_set_coeff_ui_fmpz/ /A/ /c/ /exp/ /ctx/ 
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_set_coeff_ui_fmpz"
  fmpz_mod_mpoly_set_coeff_ui_fmpz :: Ptr CFmpzModMPoly -> CULong -> Ptr (Ptr CFmpz) -> Ptr CFmpzModMPolyCtx -> IO ()
-- | /fmpz_mod_mpoly_set_coeff_si_fmpz/ /A/ /c/ /exp/ /ctx/ 
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_set_coeff_si_fmpz"
  fmpz_mod_mpoly_set_coeff_si_fmpz :: Ptr CFmpzModMPoly -> CLong -> Ptr (Ptr CFmpz) -> Ptr CFmpzModMPolyCtx -> IO ()
-- | /fmpz_mod_mpoly_set_coeff_fmpz_ui/ /A/ /c/ /exp/ /ctx/ 
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_set_coeff_fmpz_ui"
  fmpz_mod_mpoly_set_coeff_fmpz_ui :: Ptr CFmpzModMPoly -> Ptr CFmpz -> Ptr CULong -> Ptr CFmpzModMPolyCtx -> IO ()
-- | /fmpz_mod_mpoly_set_coeff_ui_ui/ /A/ /c/ /exp/ /ctx/ 
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_set_coeff_ui_ui"
  fmpz_mod_mpoly_set_coeff_ui_ui :: Ptr CFmpzModMPoly -> CULong -> Ptr CULong -> Ptr CFmpzModMPolyCtx -> IO ()
-- | /fmpz_mod_mpoly_set_coeff_si_ui/ /A/ /c/ /exp/ /ctx/ 
--
-- Set the coefficient of the monomial with exponent vector /exp/ to /c/.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_set_coeff_si_ui"
  fmpz_mod_mpoly_set_coeff_si_ui :: Ptr CFmpzModMPoly -> CLong -> Ptr CULong -> Ptr CFmpzModMPolyCtx -> IO ()

-- | /fmpz_mod_mpoly_get_coeff_vars_ui/ /C/ /A/ /vars/ /exps/ /length/ /ctx/ 
--
-- Set /C/ to the coefficient of /A/ with respect to the variables in
-- /vars/ with powers in the corresponding array /exps/. Both /vars/ and
-- /exps/ point to array of length /length/. It is assumed that
-- \(0 < length \le nvars(A)\) and that the variables in /vars/ are
-- distinct.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_get_coeff_vars_ui"
  fmpz_mod_mpoly_get_coeff_vars_ui :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> Ptr CLong -> Ptr CULong -> CLong -> Ptr CFmpzModMPolyCtx -> IO ()

-- Comparison ------------------------------------------------------------------

-- | /fmpz_mod_mpoly_cmp/ /A/ /B/ /ctx/ 
--
-- Return \(1\) (resp. \(-1\), or \(0\)) if /A/ is after (resp. before,
-- same as) /B/ in some arbitrary but fixed total ordering of the
-- polynomials. This ordering agrees with the usual ordering of monomials
-- when /A/ and /B/ are both monomials.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_cmp"
  fmpz_mod_mpoly_cmp :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> Ptr CFmpzModMPolyCtx -> IO CInt

-- Container operations --------------------------------------------------------




-- | /fmpz_mod_mpoly_is_canonical/ /A/ /ctx/ 
--
-- Return \(1\) if /A/ is in canonical form. Otherwise, return \(0\). To be
-- in canonical form, all of the terms must have nonzero coefficient, and
-- the terms must be sorted from greatest to least.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_is_canonical"
  fmpz_mod_mpoly_is_canonical :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPolyCtx -> IO CInt

-- | /fmpz_mod_mpoly_length/ /A/ /ctx/ 
--
-- Return the number of terms in /A/. If the polynomial is in canonical
-- form, this will be the number of nonzero coefficients.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_length"
  fmpz_mod_mpoly_length :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPolyCtx -> IO CLong

-- | /fmpz_mod_mpoly_resize/ /A/ /new_length/ /ctx/ 
--
-- Set the length of /A/ to @new_length@. Terms are either deleted from the
-- end, or new zero terms are appended.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_resize"
  fmpz_mod_mpoly_resize :: Ptr CFmpzModMPoly -> CLong -> Ptr CFmpzModMPolyCtx -> IO ()

-- | /fmpz_mod_mpoly_get_term_coeff_fmpz/ /c/ /A/ /i/ /ctx/ 
--
-- Set /c/ to the coefficient of the term of index /i/.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_get_term_coeff_fmpz"
  fmpz_mod_mpoly_get_term_coeff_fmpz :: Ptr CFmpz -> Ptr CFmpzModMPoly -> CLong -> Ptr CFmpzModMPolyCtx -> IO ()

-- | /fmpz_mod_mpoly_set_term_coeff_fmpz/ /A/ /i/ /c/ /ctx/ 
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_set_term_coeff_fmpz"
  fmpz_mod_mpoly_set_term_coeff_fmpz :: Ptr CFmpzModMPoly -> CLong -> Ptr CFmpz -> Ptr CFmpzModMPolyCtx -> IO ()
-- | /fmpz_mod_mpoly_set_term_coeff_ui/ /A/ /i/ /c/ /ctx/ 
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_set_term_coeff_ui"
  fmpz_mod_mpoly_set_term_coeff_ui :: Ptr CFmpzModMPoly -> CLong -> CULong -> Ptr CFmpzModMPolyCtx -> IO ()
-- | /fmpz_mod_mpoly_set_term_coeff_si/ /A/ /i/ /c/ /ctx/ 
--
-- Set the coefficient of the term of index /i/ to /c/.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_set_term_coeff_si"
  fmpz_mod_mpoly_set_term_coeff_si :: Ptr CFmpzModMPoly -> CLong -> CLong -> Ptr CFmpzModMPolyCtx -> IO ()

-- | /fmpz_mod_mpoly_term_exp_fits_si/ /poly/ /i/ /ctx/ 
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_term_exp_fits_si"
  fmpz_mod_mpoly_term_exp_fits_si :: Ptr CFmpzModMPoly -> CLong -> Ptr CFmpzModMPolyCtx -> IO CInt
-- | /fmpz_mod_mpoly_term_exp_fits_ui/ /poly/ /i/ /ctx/ 
--
-- Return \(1\) if all entries of the exponent vector of the term of index
-- /i/ fit into an @slong@ (resp. a @ulong@). Otherwise, return \(0\).
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_term_exp_fits_ui"
  fmpz_mod_mpoly_term_exp_fits_ui :: Ptr CFmpzModMPoly -> CLong -> Ptr CFmpzModMPolyCtx -> IO CInt

-- | /fmpz_mod_mpoly_get_term_exp_fmpz/ /exp/ /A/ /i/ /ctx/ 
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_get_term_exp_fmpz"
  fmpz_mod_mpoly_get_term_exp_fmpz :: Ptr (Ptr CFmpz) -> Ptr CFmpzModMPoly -> CLong -> Ptr CFmpzModMPolyCtx -> IO ()
-- | /fmpz_mod_mpoly_get_term_exp_ui/ /exp/ /A/ /i/ /ctx/ 
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_get_term_exp_ui"
  fmpz_mod_mpoly_get_term_exp_ui :: Ptr CULong -> Ptr CFmpzModMPoly -> CLong -> Ptr CFmpzModMPolyCtx -> IO ()
-- | /fmpz_mod_mpoly_get_term_exp_si/ /exp/ /A/ /i/ /ctx/ 
--
-- Set /exp/ to the exponent vector of the term of index /i/. The @_ui@
-- (resp. @_si@) version throws if any entry does not fit into a @ulong@
-- (resp. @slong@).
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_get_term_exp_si"
  fmpz_mod_mpoly_get_term_exp_si :: Ptr CLong -> Ptr CFmpzModMPoly -> CLong -> Ptr CFmpzModMPolyCtx -> IO ()

-- | /fmpz_mod_mpoly_get_term_var_exp_ui/ /A/ /i/ /var/ /ctx/ 
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_get_term_var_exp_ui"
  fmpz_mod_mpoly_get_term_var_exp_ui :: Ptr CFmpzModMPoly -> CLong -> CLong -> Ptr CFmpzModMPolyCtx -> IO CULong
-- | /fmpz_mod_mpoly_get_term_var_exp_si/ /A/ /i/ /var/ /ctx/ 
--
-- Return the exponent of the variable /var/ of the term of index /i/. This
-- function throws if the exponent does not fit into a @ulong@ (resp.
-- @slong@).
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_get_term_var_exp_si"
  fmpz_mod_mpoly_get_term_var_exp_si :: Ptr CFmpzModMPoly -> CLong -> CLong -> Ptr CFmpzModMPolyCtx -> IO CLong

-- | /fmpz_mod_mpoly_set_term_exp_fmpz/ /A/ /i/ /exp/ /ctx/ 
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_set_term_exp_fmpz"
  fmpz_mod_mpoly_set_term_exp_fmpz :: Ptr CFmpzModMPoly -> CLong -> Ptr (Ptr CFmpz) -> Ptr CFmpzModMPolyCtx -> IO ()
-- | /fmpz_mod_mpoly_set_term_exp_ui/ /A/ /i/ /exp/ /ctx/ 
--
-- Set the exponent vector of the term of index /i/ to /exp/.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_set_term_exp_ui"
  fmpz_mod_mpoly_set_term_exp_ui :: Ptr CFmpzModMPoly -> CLong -> Ptr CULong -> Ptr CFmpzModMPolyCtx -> IO ()

-- | /fmpz_mod_mpoly_get_term/ /M/ /A/ /i/ /ctx/ 
--
-- Set /M/ to the term of index /i/ in /A/.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_get_term"
  fmpz_mod_mpoly_get_term :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> CLong -> Ptr CFmpzModMPolyCtx -> IO ()

-- | /fmpz_mod_mpoly_get_term_monomial/ /M/ /A/ /i/ /ctx/ 
--
-- Set /M/ to the monomial of the term of index /i/ in /A/. The coefficient
-- of /M/ will be one.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_get_term_monomial"
  fmpz_mod_mpoly_get_term_monomial :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> CLong -> Ptr CFmpzModMPolyCtx -> IO ()

-- | /fmpz_mod_mpoly_push_term_fmpz_fmpz/ /A/ /c/ /exp/ /ctx/ 
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_push_term_fmpz_fmpz"
  fmpz_mod_mpoly_push_term_fmpz_fmpz :: Ptr CFmpzModMPoly -> Ptr CFmpz -> Ptr (Ptr CFmpz) -> Ptr CFmpzModMPolyCtx -> IO ()
-- | /fmpz_mod_mpoly_push_term_ui_fmpz/ /A/ /c/ /exp/ /ctx/ 
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_push_term_ui_fmpz"
  fmpz_mod_mpoly_push_term_ui_fmpz :: Ptr CFmpzModMPoly -> CULong -> Ptr (Ptr CFmpz) -> Ptr CFmpzModMPolyCtx -> IO ()
-- | /fmpz_mod_mpoly_push_term_si_fmpz/ /A/ /c/ /exp/ /ctx/ 
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_push_term_si_fmpz"
  fmpz_mod_mpoly_push_term_si_fmpz :: Ptr CFmpzModMPoly -> CLong -> Ptr (Ptr CFmpz) -> Ptr CFmpzModMPolyCtx -> IO ()
-- | /fmpz_mod_mpoly_push_term_fmpz_ui/ /A/ /c/ /exp/ /ctx/ 
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_push_term_fmpz_ui"
  fmpz_mod_mpoly_push_term_fmpz_ui :: Ptr CFmpzModMPoly -> Ptr CFmpz -> Ptr CULong -> Ptr CFmpzModMPolyCtx -> IO ()
-- | /fmpz_mod_mpoly_push_term_ui_ui/ /A/ /c/ /exp/ /ctx/ 
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_push_term_ui_ui"
  fmpz_mod_mpoly_push_term_ui_ui :: Ptr CFmpzModMPoly -> CULong -> Ptr CULong -> Ptr CFmpzModMPolyCtx -> IO ()
-- | /fmpz_mod_mpoly_push_term_si_ui/ /A/ /c/ /exp/ /ctx/ 
--
-- Append a term to /A/ with coefficient /c/ and exponent vector /exp/.
-- This function runs in constant average time.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_push_term_si_ui"
  fmpz_mod_mpoly_push_term_si_ui :: Ptr CFmpzModMPoly -> CLong -> Ptr CULong -> Ptr CFmpzModMPolyCtx -> IO ()

-- | /fmpz_mod_mpoly_sort_terms/ /A/ /ctx/ 
--
-- Sort the terms of /A/ into the canonical ordering dictated by the
-- ordering in /ctx/. This function simply reorders the terms: It does not
-- combine like terms, nor does it delete terms with coefficient zero. This
-- function runs in linear time in the size of /A/.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_sort_terms"
  fmpz_mod_mpoly_sort_terms :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPolyCtx -> IO ()

-- | /fmpz_mod_mpoly_combine_like_terms/ /A/ /ctx/ 
--
-- Combine adjacent like terms in /A/ and delete terms with coefficient
-- zero. If the terms of /A/ were sorted to begin with, the result will be
-- in canonical form. This function runs in linear time in the size of /A/.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_combine_like_terms"
  fmpz_mod_mpoly_combine_like_terms :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPolyCtx -> IO ()

-- -- | /fmpz_mod_mpoly_reverse/ /A/ /B/ /ctx/ 
-- --
-- -- Set /A/ to the reversal of /B/.
-- foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_reverse"
--   fmpz_mod_mpoly_reverse :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> Ptr CFmpzModMPolyCtx -> IO ()

-- Random generation -----------------------------------------------------------

-- | /fmpz_mod_mpoly_randtest_bound/ /A/ /state/ /length/ /exp_bound/ /ctx/ 
--
-- Generate a random polynomial with length up to /length/ and exponents in
-- the range @[0, exp_bound - 1]@. The exponents of each variable are
-- generated by calls to @n_randint(state, exp_bound)@.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_randtest_bound"
  fmpz_mod_mpoly_randtest_bound :: Ptr CFmpzModMPoly -> Ptr CFRandState -> CLong -> CULong -> Ptr CFmpzModMPolyCtx -> IO ()

-- | /fmpz_mod_mpoly_randtest_bounds/ /A/ /state/ /length/ /exp_bounds/ /ctx/ 
--
-- Generate a random polynomial with length up to /length/ and exponents in
-- the range @[0, exp_bounds[i] - 1]@. The exponents of the variable of
-- index /i/ are generated by calls to @n_randint(state, exp_bounds[i])@.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_randtest_bounds"
  fmpz_mod_mpoly_randtest_bounds :: Ptr CFmpzModMPoly -> Ptr CFRandState -> CLong -> Ptr CULong -> Ptr CFmpzModMPolyCtx -> IO ()

-- | /fmpz_mod_mpoly_randtest_bits/ /A/ /state/ /length/ /exp_bits/ /ctx/ 
--
-- Generate a random polynomial with length up to /length/ and exponents
-- whose packed form does not exceed the given bit count.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_randtest_bits"
  fmpz_mod_mpoly_randtest_bits :: Ptr CFmpzModMPoly -> Ptr CFRandState -> CLong -> CMpLimb -> Ptr CFmpzModMPolyCtx -> IO ()

-- Addition\/Subtraction -------------------------------------------------------

-- | /fmpz_mod_mpoly_add_fmpz/ /A/ /B/ /c/ /ctx/ 
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_add_fmpz"
  fmpz_mod_mpoly_add_fmpz :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> Ptr CFmpz -> Ptr CFmpzModMPolyCtx -> IO ()
-- | /fmpz_mod_mpoly_add_ui/ /A/ /B/ /c/ /ctx/ 
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_add_ui"
  fmpz_mod_mpoly_add_ui :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> CULong -> Ptr CFmpzModMPolyCtx -> IO ()
-- | /fmpz_mod_mpoly_add_si/ /A/ /B/ /c/ /ctx/ 
--
-- Set /A/ to \(B + c\).
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_add_si"
  fmpz_mod_mpoly_add_si :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> CLong -> Ptr CFmpzModMPolyCtx -> IO ()

-- | /fmpz_mod_mpoly_sub_fmpz/ /A/ /B/ /c/ /ctx/ 
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_sub_fmpz"
  fmpz_mod_mpoly_sub_fmpz :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> Ptr CFmpz -> Ptr CFmpzModMPolyCtx -> IO ()
-- | /fmpz_mod_mpoly_sub_ui/ /A/ /B/ /c/ /ctx/ 
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_sub_ui"
  fmpz_mod_mpoly_sub_ui :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> CULong -> Ptr CFmpzModMPolyCtx -> IO ()
-- | /fmpz_mod_mpoly_sub_si/ /A/ /B/ /c/ /ctx/ 
--
-- Set /A/ to \(B - c\).
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_sub_si"
  fmpz_mod_mpoly_sub_si :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> CLong -> Ptr CFmpzModMPolyCtx -> IO ()

-- | /fmpz_mod_mpoly_add/ /A/ /B/ /C/ /ctx/ 
--
-- Set /A/ to \(B + C\).
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_add"
  fmpz_mod_mpoly_add :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> Ptr CFmpzModMPolyCtx -> IO ()

-- | /fmpz_mod_mpoly_sub/ /A/ /B/ /C/ /ctx/ 
--
-- Set /A/ to \(B - C\).
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_sub"
  fmpz_mod_mpoly_sub :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> Ptr CFmpzModMPolyCtx -> IO ()

-- Scalar operations -----------------------------------------------------------

-- | /fmpz_mod_mpoly_neg/ /A/ /B/ /ctx/ 
--
-- Set /A/ to \(-B\).
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_neg"
  fmpz_mod_mpoly_neg :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> Ptr CFmpzModMPolyCtx -> IO ()

-- | /fmpz_mod_mpoly_scalar_mul_fmpz/ /A/ /B/ /c/ /ctx/ 
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_scalar_mul_fmpz"
  fmpz_mod_mpoly_scalar_mul_fmpz :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> Ptr CFmpz -> Ptr CFmpzModMPolyCtx -> IO ()
-- | /fmpz_mod_mpoly_scalar_mul_ui/ /A/ /B/ /c/ /ctx/ 
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_scalar_mul_ui"
  fmpz_mod_mpoly_scalar_mul_ui :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> CULong -> Ptr CFmpzModMPolyCtx -> IO ()
-- | /fmpz_mod_mpoly_scalar_mul_si/ /A/ /B/ /c/ /ctx/ 
--
-- Set /A/ to \(B \times c\).
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_scalar_mul_si"
  fmpz_mod_mpoly_scalar_mul_si :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> CLong -> Ptr CFmpzModMPolyCtx -> IO ()

-- | /fmpz_mod_mpoly_scalar_addmul_fmpz/ /A/ /B/ /C/ /d/ /ctx/ 
--
-- Sets /A/ to \(B + C \times d\).
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_scalar_addmul_fmpz"
  fmpz_mod_mpoly_scalar_addmul_fmpz :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> Ptr CFmpz -> Ptr CFmpzModMPolyCtx -> IO ()

-- | /fmpz_mod_mpoly_make_monic/ /A/ /B/ /ctx/ 
--
-- Set /A/ to /B/ divided by the leading coefficient of /B/. This throws if
-- /B/ is zero or the leading coefficient is not invertible.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_make_monic"
  fmpz_mod_mpoly_make_monic :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> Ptr CFmpzModMPolyCtx -> IO ()

-- Differentiation -------------------------------------------------------------

-- | /fmpz_mod_mpoly_derivative/ /A/ /B/ /var/ /ctx/ 
--
-- Set /A/ to the derivative of /B/ with respect to the variable of index
-- /var/.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_derivative"
  fmpz_mod_mpoly_derivative :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> CLong -> Ptr CFmpzModMPolyCtx -> IO ()

-- Evaluation ------------------------------------------------------------------




-- | /fmpz_mod_mpoly_evaluate_all_fmpz/ /eval/ /A/ /vals/ /ctx/ 
--
-- Set /ev/ to the evaluation of /A/ where the variables are replaced by
-- the corresponding elements of the array /vals/.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_evaluate_all_fmpz"
  fmpz_mod_mpoly_evaluate_all_fmpz :: Ptr CFmpz -> Ptr CFmpzModMPoly -> Ptr (Ptr CFmpz) -> Ptr CFmpzModMPolyCtx -> IO ()

-- | /fmpz_mod_mpoly_evaluate_one_fmpz/ /A/ /B/ /var/ /val/ /ctx/ 
--
-- Set /A/ to the evaluation of /B/ where the variable of index /var/ is
-- replaced by /val/. Return \(1\) for success and \(0\) for failure.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_evaluate_one_fmpz"
  fmpz_mod_mpoly_evaluate_one_fmpz :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> CLong -> Ptr CFmpz -> Ptr CFmpzModMPolyCtx -> IO ()

-- -- | /fmpz_mod_mpoly_compose_fmpz_poly/ /A/ /B/ /C/ /ctxB/ 
-- --
-- -- Set /A/ to the evaluation of /B/ where the variables are replaced by the
-- -- corresponding elements of the array /C/. The context object of /B/ is
-- -- /ctxB/. Return \(1\) for success and \(0\) for failure.
-- foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_compose_fmpz_poly"
--   fmpz_mod_mpoly_compose_fmpz_poly :: Ptr CFmpzPoly -> Ptr CFmpzModMPoly -> Ptr (Ptr CFmpzPoly) -> Ptr CFmpzModMPolyCtx -> IO CInt

-- | /fmpz_mod_mpoly_compose_fmpz_mod_mpoly_geobucket/ /A/ /B/ /C/ /ctxB/ /ctxAC/ 
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_compose_fmpz_mod_mpoly_geobucket"
  fmpz_mod_mpoly_compose_fmpz_mod_mpoly_geobucket :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> Ptr (Ptr (Ptr CFmpzModMPoly)) -> Ptr CFmpzModMPolyCtx -> Ptr CFmpzModMPolyCtx -> IO CInt
-- | /fmpz_mod_mpoly_compose_fmpz_mod_mpoly/ /A/ /B/ /C/ /ctxB/ /ctxAC/ 
--
-- Set /A/ to the evaluation of /B/ where the variables are replaced by the
-- corresponding elements of the array /C/. Both /A/ and the elements of
-- /C/ have context object /ctxAC/, while /B/ has context object /ctxB/.
-- The length of the array /C/ is the number of variables in /ctxB/.
-- Neither /A/ nor /B/ is allowed to alias any other polynomial. Return
-- \(1\) for success and \(0\) for failure. The main method attempts to
-- perform the calculation using matrices and chooses heuristically between
-- the @geobucket@ and @horner@ methods if needed.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_compose_fmpz_mod_mpoly"
  fmpz_mod_mpoly_compose_fmpz_mod_mpoly :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> Ptr (Ptr (Ptr CFmpzModMPoly)) -> Ptr CFmpzModMPolyCtx -> Ptr CFmpzModMPolyCtx -> IO CInt

-- -- | /fmpz_mod_mpoly_compose_fmpz_mod_mpoly_gen/ /A/ /B/ /c/ /ctxB/ /ctxAC/ 
-- --
-- -- Set /A/ to the evaluation of /B/ where the variable of index /i/ in
-- -- /ctxB/ is replaced by the variable of index @c[i]@ in /ctxAC/. The
-- -- length of the array /C/ is the number of variables in /ctxB/. If any
-- -- @c[i]@ is negative, the corresponding variable of /B/ is replaced by
-- -- zero. Otherwise, it is expected that @c[i]@ is less than the number of
-- -- variables in /ctxAC/.
-- foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_compose_fmpz_mod_mpoly_gen"
--   fmpz_mod_mpoly_compose_fmpz_mod_mpoly_gen :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> Ptr CLong -> Ptr CFmpzModMPolyCtx -> Ptr CFmpzModMPolyCtx -> IO ()

-- Multiplication --------------------------------------------------------------

-- | /fmpz_mod_mpoly_mul/ /A/ /B/ /C/ /ctx/ 
--
-- Set /A/ to \(B \times C\).
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_mul"
  fmpz_mod_mpoly_mul :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> Ptr CFmpzModMPolyCtx -> IO ()

-- | /fmpz_mod_mpoly_mul_johnson/ /A/ /B/ /C/ /ctx/ 
--
-- Set /A/ to \(B \times C\) using Johnson\'s heap-based method.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_mul_johnson"
  fmpz_mod_mpoly_mul_johnson :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> Ptr CFmpzModMPolyCtx -> IO ()

-- | /fmpz_mod_mpoly_mul_dense/ /A/ /B/ /C/ /ctx/ 
--
-- Try to set /A/ to \(B \times C\) using dense arithmetic. If the return
-- is \(0\), the operation was unsuccessful. Otherwise, it was successful
-- and the return is \(1\).
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_mul_dense"
  fmpz_mod_mpoly_mul_dense :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> Ptr CFmpzModMPolyCtx -> IO CInt

-- Powering --------------------------------------------------------------------




-- | /fmpz_mod_mpoly_pow_fmpz/ /A/ /B/ /k/ /ctx/ 
--
-- Set /A/ to /B/ raised to the \(k\)-th power. Return \(1\) for success
-- and \(0\) for failure.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_pow_fmpz"
  fmpz_mod_mpoly_pow_fmpz :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> Ptr CFmpz -> Ptr CFmpzModMPolyCtx -> IO CInt

-- | /fmpz_mod_mpoly_pow_ui/ /A/ /B/ /k/ /ctx/ 
--
-- Set /A/ to /B/ raised to the \(k\)-th power. Return \(1\) for success
-- and \(0\) for failure.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_pow_ui"
  fmpz_mod_mpoly_pow_ui :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> CULong -> Ptr CFmpzModMPolyCtx -> IO CInt

-- Division --------------------------------------------------------------------

-- The division functions assume that the modulus is prime.
--
-- | /fmpz_mod_mpoly_divides/ /Q/ /A/ /B/ /ctx/ 
--
-- If /A/ is divisible by /B/, set /Q/ to the exact quotient and return
-- \(1\). Otherwise, set /Q/ to zero and return \(0\).
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_divides"
  fmpz_mod_mpoly_divides :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> Ptr CFmpzModMPolyCtx -> IO CInt

-- | /fmpz_mod_mpoly_div/ /Q/ /A/ /B/ /ctx/ 
--
-- Set /Q/ to the quotient of /A/ by /B/, discarding the remainder.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_div"
  fmpz_mod_mpoly_div :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> Ptr CFmpzModMPolyCtx -> IO ()

-- | /fmpz_mod_mpoly_divrem/ /Q/ /R/ /A/ /B/ /ctx/ 
--
-- Set /Q/ and /R/ to the quotient and remainder of /A/ divided by /B/.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_divrem"
  fmpz_mod_mpoly_divrem :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> Ptr CFmpzModMPolyCtx -> IO ()

-- | /fmpz_mod_mpoly_divrem_ideal/ /Q/ /R/ /A/ /B/ /len/ /ctx/ 
--
-- This function is as per @fmpz_mod_mpoly_divrem@ except that it takes an
-- array of divisor polynomials /B/ and it returns an array of quotient
-- polynomials /Q/. The number of divisor (and hence quotient) polynomials,
-- is given by /len/.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_divrem_ideal"
  fmpz_mod_mpoly_divrem_ideal :: Ptr (Ptr (Ptr CFmpzModMPoly)) -> Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> Ptr (Ptr (Ptr CFmpzModMPoly)) -> CLong -> Ptr CFmpzModMPolyCtx -> IO ()

-- Greatest Common Divisor -----------------------------------------------------

-- | /fmpz_mod_mpoly_term_content/ /M/ /A/ /ctx/ 
--
-- Set /M/ to the GCD of the terms of /A/. If /A/ is zero, /M/ will be
-- zero. Otherwise, /M/ will be a monomial with coefficient one.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_term_content"
  fmpz_mod_mpoly_term_content :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> Ptr CFmpzModMPolyCtx -> IO ()

-- | /fmpz_mod_mpoly_content_vars/ /g/ /A/ /vars/ /vars_length/ /ctx/ 
--
-- Set /g/ to the GCD of the coefficients of /A/ when viewed as a
-- polynomial in the variables /vars/. Return \(1\) for success and \(0\)
-- for failure. Upon success, /g/ will be independent of the variables
-- /vars/.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_content_vars"
  fmpz_mod_mpoly_content_vars :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> Ptr CLong -> CLong -> Ptr CFmpzModMPolyCtx -> IO CInt

-- | /fmpz_mod_mpoly_gcd/ /G/ /A/ /B/ /ctx/ 
--
-- Try to set /G/ to the monic GCD of /A/ and /B/. The GCD of zero and zero
-- is defined to be zero. If the return is \(1\) the function was
-- successful. Otherwise the return is \(0\) and /G/ is left untouched.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_gcd"
  fmpz_mod_mpoly_gcd :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> Ptr CFmpzModMPolyCtx -> IO CInt

-- | /fmpz_mod_mpoly_gcd_cofactors/ /G/ /Abar/ /Bbar/ /A/ /B/ /ctx/ 
--
-- Do the operation of @fmpz_mod_mpoly_gcd@ and also compute \(Abar = A/G\)
-- and \(Bbar = B/G\) if successful.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_gcd_cofactors"
  fmpz_mod_mpoly_gcd_cofactors :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> Ptr CFmpzModMPolyCtx -> IO CInt

-- | /fmpz_mod_mpoly_gcd_brown/ /G/ /A/ /B/ /ctx/ 
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_gcd_brown"
  fmpz_mod_mpoly_gcd_brown :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> Ptr CFmpzModMPolyCtx -> IO CInt
-- | /fmpz_mod_mpoly_gcd_hensel/ /G/ /A/ /B/ /ctx/ 
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_gcd_hensel"
  fmpz_mod_mpoly_gcd_hensel :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> Ptr CFmpzModMPolyCtx -> IO CInt
-- | /fmpz_mod_mpoly_gcd_subresultant/ /G/ /A/ /B/ /ctx/ 
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_gcd_subresultant"
  fmpz_mod_mpoly_gcd_subresultant :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> Ptr CFmpzModMPolyCtx -> IO CInt
-- | /fmpz_mod_mpoly_gcd_zippel/ /G/ /A/ /B/ /ctx/ 
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_gcd_zippel"
  fmpz_mod_mpoly_gcd_zippel :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> Ptr CFmpzModMPolyCtx -> IO CInt
-- | /fmpz_mod_mpoly_gcd_zippel2/ /G/ /A/ /B/ /ctx/ 
--
-- Try to set /G/ to the GCD of /A/ and /B/ using various algorithms.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_gcd_zippel2"
  fmpz_mod_mpoly_gcd_zippel2 :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> Ptr CFmpzModMPolyCtx -> IO CInt

-- | /fmpz_mod_mpoly_resultant/ /R/ /A/ /B/ /var/ /ctx/ 
--
-- Try to set /R/ to the resultant of /A/ and /B/ with respect to the
-- variable of index /var/.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_resultant"
  fmpz_mod_mpoly_resultant :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> CLong -> Ptr CFmpzModMPolyCtx -> IO CInt

-- | /fmpz_mod_mpoly_discriminant/ /D/ /A/ /var/ /ctx/ 
--
-- Try to set /D/ to the discriminant of /A/ with respect to the variable
-- of index /var/.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_discriminant"
  fmpz_mod_mpoly_discriminant :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> CLong -> Ptr CFmpzModMPolyCtx -> IO CInt

-- Square Root -----------------------------------------------------------------

-- The square root functions assume that the modulus is prime for correct
-- operation.
--
-- | /fmpz_mod_mpoly_sqrt/ /Q/ /A/ /ctx/ 
--
-- If \(Q^2=A\) has a solution, set /Q/ to a solution and return \(1\),
-- otherwise return \(0\) and set /Q/ to zero.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_sqrt"
  fmpz_mod_mpoly_sqrt :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> Ptr CFmpzModMPolyCtx -> IO CInt

-- | /fmpz_mod_mpoly_is_square/ /A/ /ctx/ 
--
-- Return \(1\) if /A/ is a perfect square, otherwise return \(0\).
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_is_square"
  fmpz_mod_mpoly_is_square :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPolyCtx -> IO CInt

-- | /fmpz_mod_mpoly_quadratic_root/ /Q/ /A/ /B/ /ctx/ 
--
-- If \(Q^2+AQ=B\) has a solution, set /Q/ to a solution and return \(1\),
-- otherwise return \(0\).
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_quadratic_root"
  fmpz_mod_mpoly_quadratic_root :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> Ptr CFmpzModMPolyCtx -> IO CInt

-- Univariate Functions --------------------------------------------------------

-- | /fmpz_mod_mpoly_univar_init/ /A/ /ctx/ 
--
-- Initialize /A/.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_univar_init"
  fmpz_mod_mpoly_univar_init :: Ptr CFmpzModMPolyUnivar -> Ptr CFmpzModMPolyCtx -> IO ()

-- | /fmpz_mod_mpoly_univar_clear/ /A/ /ctx/ 
--
-- Clear /A/.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_univar_clear"
  fmpz_mod_mpoly_univar_clear :: Ptr CFmpzModMPolyUnivar -> Ptr CFmpzModMPolyCtx -> IO ()

foreign import ccall "fmpz_mod_mpoly.h &fmpz_mod_mpoly_univar_clear"
  p_fmpz_mod_mpoly_univar_clear :: FunPtr (Ptr CFmpzModMPolyUnivar -> Ptr CFmpzModMPolyCtx -> IO ())
  
-- | /fmpz_mod_mpoly_univar_swap/ /A/ /B/ /ctx/ 
--
-- Swap /A/ and /B/.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_univar_swap"
  fmpz_mod_mpoly_univar_swap :: Ptr CFmpzModMPolyUnivar -> Ptr CFmpzModMPolyUnivar -> Ptr CFmpzModMPolyCtx -> IO ()

-- | /fmpz_mod_mpoly_to_univar/ /A/ /B/ /var/ /ctx/ 
--
-- Set /A/ to a univariate form of /B/ by pulling out the variable of index
-- /var/. The coefficients of /A/ will still belong to the content /ctx/
-- but will not depend on the variable of index /var/.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_to_univar"
  fmpz_mod_mpoly_to_univar :: Ptr CFmpzModMPolyUnivar -> Ptr CFmpzModMPoly -> CLong -> Ptr CFmpzModMPolyCtx -> IO ()

-- | /fmpz_mod_mpoly_from_univar/ /A/ /B/ /var/ /ctx/ 
--
-- Set /A/ to the normal form of /B/ by putting in the variable of index
-- /var/. This function is undefined if the coefficients of /B/ depend on
-- the variable of index /var/.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_from_univar"
  fmpz_mod_mpoly_from_univar :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPolyUnivar -> CLong -> Ptr CFmpzModMPolyCtx -> IO ()

-- | /fmpz_mod_mpoly_univar_degree_fits_si/ /A/ /ctx/ 
--
-- Return \(1\) if the degree of /A/ with respect to the main variable fits
-- an @slong@. Otherwise, return \(0\).
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_univar_degree_fits_si"
  fmpz_mod_mpoly_univar_degree_fits_si :: Ptr CFmpzModMPolyUnivar -> Ptr CFmpzModMPolyCtx -> IO CInt

-- | /fmpz_mod_mpoly_univar_length/ /A/ /ctx/ 
--
-- Return the number of terms in /A/ with respect to the main variable.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_univar_length"
  fmpz_mod_mpoly_univar_length :: Ptr CFmpzModMPolyUnivar -> Ptr CFmpzModMPolyCtx -> IO CLong

-- | /fmpz_mod_mpoly_univar_get_term_exp_si/ /A/ /i/ /ctx/ 
--
-- Return the exponent of the term of index /i/ of /A/.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_univar_get_term_exp_si"
  fmpz_mod_mpoly_univar_get_term_exp_si :: Ptr CFmpzModMPolyUnivar -> CLong -> Ptr CFmpzModMPolyCtx -> IO CLong

-- | /fmpz_mod_mpoly_univar_get_term_coeff/ /c/ /A/ /i/ /ctx/ 
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_univar_get_term_coeff"
  fmpz_mod_mpoly_univar_get_term_coeff :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPolyUnivar -> CLong -> Ptr CFmpzModMPolyCtx -> IO ()
-- | /fmpz_mod_mpoly_univar_swap_term_coeff/ /c/ /A/ /i/ /ctx/ 
--
-- Set (resp. swap) /c/ to (resp. with) the coefficient of the term of
-- index /i/ of /A/.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_univar_swap_term_coeff"
  fmpz_mod_mpoly_univar_swap_term_coeff :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPolyUnivar -> CLong -> Ptr CFmpzModMPolyCtx -> IO ()

-- | /fmpz_mod_mpoly_univar_set_coeff_ui/ /Ax/ /e/ /c/ /ctx/ 
--
-- Set the coefficient of \(X^e\) in /Ax/ to /c/.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_univar_set_coeff_ui"
  fmpz_mod_mpoly_univar_set_coeff_ui :: Ptr CFmpzModMPolyUnivar -> CULong -> Ptr CFmpzModMPoly -> Ptr CFmpzModMPolyCtx -> IO ()

-- | /fmpz_mod_mpoly_univar_resultant/ /R/ /Ax/ /Bx/ /ctx/ 
--
-- Try to set /R/ to the resultant of /Ax/ and /Bx/.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_univar_resultant"
  fmpz_mod_mpoly_univar_resultant :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPolyUnivar -> Ptr CFmpzModMPolyUnivar -> Ptr CFmpzModMPolyCtx -> IO CInt

-- | /fmpz_mod_mpoly_univar_discriminant/ /D/ /Ax/ /ctx/ 
--
-- Try to set /D/ to the discriminant of /Ax/.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_univar_discriminant"
  fmpz_mod_mpoly_univar_discriminant :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPolyUnivar -> Ptr CFmpzModMPolyCtx -> IO CInt

-- Internal Functions ----------------------------------------------------------

-- | /fmpz_mod_mpoly_inflate/ /A/ /B/ /shift/ /stride/ /ctx/ 
--
-- Apply the function @e -> shift[v] + stride[v]*e@ to each exponent @e@
-- corresponding to the variable @v@. It is assumed that each shift and
-- stride is not negative.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_inflate"
  fmpz_mod_mpoly_inflate :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpzModMPolyCtx -> IO ()

-- | /fmpz_mod_mpoly_deflate/ /A/ /B/ /shift/ /stride/ /ctx/ 
--
-- Apply the function @e -> (e - shift[v])\/stride[v]@ to each exponent @e@
-- corresponding to the variable @v@. If any @stride[v]@ is zero, the
-- corresponding numerator @e - shift[v]@ is assumed to be zero, and the
-- quotient is defined as zero. This allows the function to undo the
-- operation performed by @fmpz_mod_mpoly_inflate@ when possible.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_deflate"
  fmpz_mod_mpoly_deflate :: Ptr CFmpzModMPoly -> Ptr CFmpzModMPoly -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpzModMPolyCtx -> IO ()

-- | /fmpz_mod_mpoly_deflation/ /shift/ /stride/ /A/ /ctx/ 
--
-- For each variable \(v\) let \(S_v\) be the set of exponents appearing on
-- \(v\). Set @shift[v]@ to \(\operatorname{min}(S_v)\) and set @stride[v]@
-- to \(\operatorname{gcd}(S-\operatorname{min}(S_v))\). If /A/ is zero,
-- all shifts and strides are set to zero.
foreign import ccall "fmpz_mod_mpoly.h fmpz_mod_mpoly_deflation"
  fmpz_mod_mpoly_deflation :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpzModMPoly -> Ptr CFmpzModMPolyCtx -> IO ()

