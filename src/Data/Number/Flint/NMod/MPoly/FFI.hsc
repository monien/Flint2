{-|
module      :  Data.Number.Flint.NMod.MPoly.FFI
copyright   :  (c) 2022 Hartmut Monien
license     :  GNU GPL, version 2 or above (see LICENSE)
maintainer  :  hmonien@uni-bonn.de
-}
module Data.Number.Flint.NMod.MPoly.FFI (
  -- * Multivariate polynomials over integers mod n (word-size n)
    NModMPoly (..)
  , CNModMPoly (..)
  , newNModMPoly
  , withNModMPoly
  -- * Context object
  , NModMPolyCtx (..)
  , CNModMPolyCtx (..)
  , newNModMPolyCtx
  , withNModMPolyCtx
  , nmod_mpoly_ctx_init
  , nmod_mpoly_ctx_nvars
  , nmod_mpoly_ctx_ord
  , nmod_mpoly_ctx_modulus
  , nmod_mpoly_ctx_clear
  -- * Memory management
  , nmod_mpoly_init
  , nmod_mpoly_init2
  , nmod_mpoly_init3
  , nmod_mpoly_fit_length
  , nmod_mpoly_realloc
  , nmod_mpoly_clear
  -- * Input\/Output
  , nmod_mpoly_get_str_pretty
  , nmod_mpoly_fprint_pretty
  , nmod_mpoly_print_pretty
  , nmod_mpoly_set_str_pretty
  -- * Basic manipulation
  , nmod_mpoly_gen
  , nmod_mpoly_is_gen
  , nmod_mpoly_set
  , nmod_mpoly_equal
  , nmod_mpoly_swap
  -- * Constants
  , nmod_mpoly_is_ui
  , nmod_mpoly_get_ui
  , nmod_mpoly_set_ui
  , nmod_mpoly_zero
  , nmod_mpoly_one
  , nmod_mpoly_equal_ui
  , nmod_mpoly_is_zero
  , nmod_mpoly_is_one
  -- * Degrees
  , nmod_mpoly_degrees_fit_si
  , nmod_mpoly_degrees_fmpz
  , nmod_mpoly_degrees_si
  , nmod_mpoly_degree_fmpz
  , nmod_mpoly_degree_si
  , nmod_mpoly_total_degree_fits_si
  , nmod_mpoly_total_degree_fmpz
  , nmod_mpoly_total_degree_si
  , nmod_mpoly_used_vars
  -- * Coefficients
  , nmod_mpoly_get_coeff_ui_monomial
  , nmod_mpoly_set_coeff_ui_monomial
  , nmod_mpoly_get_coeff_ui_fmpz
  , nmod_mpoly_get_coeff_ui_ui
  , nmod_mpoly_set_coeff_ui_fmpz
  , nmod_mpoly_set_coeff_ui_ui
  , nmod_mpoly_get_coeff_vars_ui
  -- * Comparison
  , nmod_mpoly_cmp
  -- * Container operations
  , nmod_mpoly_term_coeff_ref
  , nmod_mpoly_is_canonical
  , nmod_mpoly_length
  , nmod_mpoly_resize
  , nmod_mpoly_get_term_coeff_ui
  , nmod_mpoly_set_term_coeff_ui
  , nmod_mpoly_term_exp_fits_si
  , nmod_mpoly_term_exp_fits_ui
  , nmod_mpoly_get_term_exp_fmpz
  , nmod_mpoly_get_term_exp_ui
  , nmod_mpoly_get_term_exp_si
  , nmod_mpoly_get_term_var_exp_ui
  , nmod_mpoly_get_term_var_exp_si
  , nmod_mpoly_set_term_exp_fmpz
  , nmod_mpoly_set_term_exp_ui
  , nmod_mpoly_get_term
  , nmod_mpoly_get_term_monomial
  , nmod_mpoly_push_term_ui_fmpz
  , nmod_mpoly_push_term_ui_ui
  , nmod_mpoly_sort_terms
  , nmod_mpoly_combine_like_terms
  , nmod_mpoly_reverse
  -- * Random generation
  , nmod_mpoly_randtest_bound
  , nmod_mpoly_randtest_bounds
  , nmod_mpoly_randtest_bits
  -- * Addition\/Subtraction
  , nmod_mpoly_add_ui
  , nmod_mpoly_sub_ui
  , nmod_mpoly_add
  , nmod_mpoly_sub
  -- * Scalar operations
  , nmod_mpoly_neg
  , nmod_mpoly_scalar_mul_ui
  , nmod_mpoly_make_monic
  -- * Differentiation
  , nmod_mpoly_derivative
  -- * Evaluation
  , nmod_mpoly_evaluate_all_ui
  , nmod_mpoly_evaluate_one_ui
  , nmod_mpoly_compose_nmod_poly
  , nmod_mpoly_compose_nmod_mpoly_geobucket
  , nmod_mpoly_compose_nmod_mpoly_horner
  , nmod_mpoly_compose_nmod_mpoly
  , nmod_mpoly_compose_nmod_mpoly_gen
  -- * Multiplication
  , nmod_mpoly_mul
  , nmod_mpoly_mul_johnson
  , nmod_mpoly_mul_heap_threaded
  , nmod_mpoly_mul_array
  , nmod_mpoly_mul_array_threaded
  , nmod_mpoly_mul_dense
  -- * Powering
  , nmod_mpoly_pow_fmpz
  , nmod_mpoly_pow_ui
  -- * Division
  , nmod_mpoly_divides
  , nmod_mpoly_div
  , nmod_mpoly_divrem
  , nmod_mpoly_divrem_ideal
  , nmod_mpoly_divides_dense
  , nmod_mpoly_divides_monagan_pearce
  , nmod_mpoly_divides_heap_threaded
  -- * Greatest Common Divisor
  , nmod_mpoly_term_content
  , nmod_mpoly_content_vars
  , nmod_mpoly_gcd
  , nmod_mpoly_gcd_cofactors
  , nmod_mpoly_gcd_brown
  , nmod_mpoly_gcd_hensel
  , nmod_mpoly_gcd_zippel
  , nmod_mpoly_resultant
  , nmod_mpoly_discriminant
  -- * Square Root
  , nmod_mpoly_sqrt
  , nmod_mpoly_is_square
  , nmod_mpoly_quadratic_root
  -- * Univariate Functions
  , nmod_mpoly_univar_init
  , nmod_mpoly_univar_clear
  , nmod_mpoly_univar_swap
  , nmod_mpoly_to_univar
  , nmod_mpoly_from_univar
  , nmod_mpoly_univar_degree_fits_si
  , nmod_mpoly_univar_length
  , nmod_mpoly_univar_get_term_exp_si
  , nmod_mpoly_univar_get_term_coeff
  , nmod_mpoly_univar_swap_term_coeff
  -- * Internal Functions
  , nmod_mpoly_pow_rmul
  , nmod_mpoly_div_monagan_pearce
  , nmod_mpoly_divrem_monagan_pearce
  , nmod_mpoly_divrem_ideal_monagan_pearce
) where

-- Multivariate polynomials over integers mod n (word-size n) ------------------

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
import Data.Number.Flint.MPoly
import Data.Number.Flint.NMod
import Data.Number.Flint.NMod.Types

#include <flint/flint.h>
#include <flint/nmod.h>
#include <flint/nmod_poly.h>
#include <flint/nmod_mpoly.h>

-- nmod_mpoly_t ----------------------------------------------------------------

data NModMPoly = NModMPoly {-# UNPACK #-} !(ForeignPtr CNModMPoly)
data CNModMPoly = CNModMPoly 

instance Storable CNModMPoly where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size nmod_mpoly_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment nmod_mpoly_t}
  peek = error "CNModMPoly.peek: Not defined"
  poke = error "CNModMPoly.poke: Not defined"

-- | Create a new `NModMPoly`
newNModMPoly ctx@(NModMPolyCtx pctx) = do
  p <- mallocForeignPtr
  withForeignPtr p $ \p ->
    withNModMPolyCtx ctx $ \ctx -> do 
      nmod_mpoly_init p ctx
      addForeignPtrFinalizerEnv p_nmod_mpoly_clear p pctx 
  return $ NModMPoly p

{-# INLINE withNModMPoly #-}
withNModMPoly (NModMPoly p) f = do
  withForeignPtr p $ \fp -> (NModMPoly p,) <$> f fp

-- nmod_mpoly_univar_t ---------------------------------------------------------

data NModMPolyUnivar = NModMPolyUnivar {-# UNPACK #-} !(ForeignPtr CNModMPolyUnivar)
data CNModMPolyUnivar = CNModMPolyUnivar 

instance Storable CNModMPolyUnivar where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size nmod_mpoly_univar_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment nmod_mpoly_univar_t}
  peek = error "CNModMPolyUnivar.peek: Not defined"
  poke = error "CNModMPolyUnivar.poke: Not defined"

-- | Create a new `NModMPolyUnivar`
newNModMPolyUnivar ctx@(NModMPolyCtx pctx) = do
  p <- mallocForeignPtr
  withForeignPtr p $ \p ->
    withNModMPolyCtx ctx $ \ctx -> do 
      nmod_mpoly_univar_init p ctx
      addForeignPtrFinalizerEnv p_nmod_mpoly_univar_clear p pctx
  return $ NModMPolyUnivar p

{-# INLINE withNModMPolyUnivar #-}
withNModMPolyUnivar (NModMPolyUnivar p) f = do
  withForeignPtr p $ \fp -> (NModMPolyUnivar p,) <$> f fp

-- nmod_mpoly_ctx_t ------------------------------------------------------------

data NModMPolyCtx = NModMPolyCtx {-# UNPACK #-} !(ForeignPtr CNModMPolyCtx)
data CNModMPolyCtx

instance Storable CNModMPolyCtx where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size nmod_mpoly_ctx_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment nmod_mpoly_ctx_t}
  peek = error "CNModMPolyCtx.peek: Not defined"
  poke = error "CNModMPolyCtx.poke: Not defined"

-- | Create a new `NModMPolyCtx`
newNModMPolyCtx nvars ord n = do
  p <- mallocForeignPtr
  withForeignPtr p $ \p ->
    nmod_mpoly_ctx_init p nvars ord n
  addForeignPtrFinalizer p_nmod_mpoly_ctx_clear p
  return $ NModMPolyCtx p

-- | Use a `NModMPolyCtx`
{-# INLINE withNModMPolyCtx #-}
withNModMPolyCtx (NModMPolyCtx p) f = do
  withForeignPtr p $ \fp -> f fp >>= return . (NModMPolyCtx p,)

-- Context object --------------------------------------------------------------

-- | /nmod_mpoly_ctx_init/ /ctx/ /nvars/ /ord/ /n/ 
--
-- Initialise a context object for a polynomial ring with the given number
-- of variables and the given ordering. It will have coefficients modulo
-- /n/. Setting \(n = 0\) will give undefined behavior. The possibilities
-- for the ordering are @ORD_LEX@, @ORD_DEGLEX@ and @ORD_DEGREVLEX@.
foreign import ccall "nmod_mpoly.h nmod_mpoly_ctx_init"
  nmod_mpoly_ctx_init :: Ptr CNModMPolyCtx -> CLong -> Ptr COrdering -> CMpLimb -> IO ()

-- | /nmod_mpoly_ctx_nvars/ /ctx/ 
--
-- Return the number of variables used to initialize the context.
foreign import ccall "nmod_mpoly.h nmod_mpoly_ctx_nvars"
  nmod_mpoly_ctx_nvars :: Ptr CNModMPolyCtx -> IO CLong

-- | /nmod_mpoly_ctx_ord/ /ctx/ 
--
-- Return the ordering used to initialize the context.
foreign import ccall "nmod_mpoly.h nmod_mpoly_ctx_ord"
  nmod_mpoly_ctx_ord :: Ptr CNModMPolyCtx -> IO (Ptr COrdering)

-- | /nmod_mpoly_ctx_modulus/ /ctx/ 
--
-- Return the modulus used to initialize the context.
foreign import ccall "nmod_mpoly.h nmod_mpoly_ctx_modulus"
  nmod_mpoly_ctx_modulus :: Ptr CNModMPolyCtx -> IO CMpLimb

-- | /nmod_mpoly_ctx_clear/ /ctx/ 
--
-- Release any space allocated by /ctx/.
foreign import ccall "nmod_mpoly.h nmod_mpoly_ctx_clear"
  nmod_mpoly_ctx_clear :: Ptr CNModMPolyCtx -> IO ()

foreign import ccall "nmod_mpoly.h &nmod_mpoly_ctx_clear"
  p_nmod_mpoly_ctx_clear :: FunPtr (Ptr CNModMPolyCtx -> IO ())

-- Memory management -----------------------------------------------------------

-- | /nmod_mpoly_init/ /A/ /ctx/ 
--
-- Initialise /A/ for use with the given an initialised context object. Its
-- value is set to zero.
foreign import ccall "nmod_mpoly.h nmod_mpoly_init"
  nmod_mpoly_init :: Ptr CNModMPoly -> Ptr CNModMPolyCtx -> IO ()

-- | /nmod_mpoly_init2/ /A/ /alloc/ /ctx/ 
--
-- Initialise /A/ for use with the given an initialised context object. Its
-- value is set to zero. It is allocated with space for /alloc/ terms and
-- at least @MPOLY_MIN_BITS@ bits for the exponent widths.
foreign import ccall "nmod_mpoly.h nmod_mpoly_init2"
  nmod_mpoly_init2 :: Ptr CNModMPoly -> CLong -> Ptr CNModMPolyCtx -> IO ()

-- | /nmod_mpoly_init3/ /A/ /alloc/ /bits/ /ctx/ 
--
-- Initialise /A/ for use with the given an initialised context object. Its
-- value is set to zero. It is allocated with space for /alloc/ terms and
-- /bits/ bits for the exponents.
foreign import ccall "nmod_mpoly.h nmod_mpoly_init3"
  nmod_mpoly_init3 :: Ptr CNModMPoly -> CLong -> CFBitCnt -> Ptr CNModMPolyCtx -> IO ()

-- | /nmod_mpoly_fit_length/ /A/ /len/ /ctx/ 
--
-- Ensure that /A/ has space for at least /len/ terms.
foreign import ccall "nmod_mpoly.h nmod_mpoly_fit_length"
  nmod_mpoly_fit_length :: Ptr CNModMPoly -> CLong -> Ptr CNModMPolyCtx -> IO ()

-- | /nmod_mpoly_realloc/ /A/ /alloc/ /ctx/ 
--
-- Reallocate /A/ to have space for /alloc/ terms. Assumes the current
-- length of the polynomial is not greater than /alloc/.
foreign import ccall "nmod_mpoly.h nmod_mpoly_realloc"
  nmod_mpoly_realloc :: Ptr CNModMPoly -> CLong -> Ptr CNModMPolyCtx -> IO ()

-- | /nmod_mpoly_clear/ /A/ /ctx/ 
--
-- Release any space allocated for /A/.
foreign import ccall "nmod_mpoly.h nmod_mpoly_clear"
  nmod_mpoly_clear :: Ptr CNModMPoly -> Ptr CNModMPolyCtx -> IO ()

foreign import ccall "nmod_mpoly.h &nmod_mpoly_clear"
  p_nmod_mpoly_clear :: FunPtr (Ptr CNModMPoly -> Ptr CNModMPolyCtx -> IO ())

-- Input\/Output ---------------------------------------------------------------

-- | /nmod_mpoly_get_str_pretty/ /A/ /x/ /ctx/ 
--
-- Return a string, which the user is responsible for cleaning up,
-- representing /A/, given an array of variable strings /x/.
foreign import ccall "nmod_mpoly.h nmod_mpoly_get_str_pretty"
  nmod_mpoly_get_str_pretty :: Ptr CNModMPoly -> Ptr (Ptr CChar) -> Ptr CNModMPolyCtx -> IO CString

-- | /nmod_mpoly_fprint_pretty/ /file/ /A/ /x/ /ctx/ 
--
-- Print a string representing /A/ to /file/.
foreign import ccall "nmod_mpoly.h nmod_mpoly_fprint_pretty"
  nmod_mpoly_fprint_pretty :: Ptr CFile -> Ptr CNModMPoly -> Ptr (Ptr CChar) -> Ptr CNModMPolyCtx -> IO CInt

-- | /nmod_mpoly_print_pretty/ /A/ /x/ /ctx/ 
--
-- Print a string representing /A/ to @stdout@.
nmod_mpoly_print_pretty :: Ptr CNModMPoly
                        -> Ptr (Ptr CChar)
                        -> Ptr CNModMPolyCtx
                        -> IO CInt
nmod_mpoly_print_pretty a x ctx =
  printCStr (\a -> nmod_mpoly_get_str_pretty a x ctx) a

-- | /nmod_mpoly_set_str_pretty/ /A/ /str/ /x/ /ctx/ 
--
-- Set /A/ to the polynomial in the null-terminates string /str/ given an
-- array /x/ of variable strings. If parsing /str/ fails, /A/ is set to
-- zero, and \(-1\) is returned. Otherwise, \(0\) is returned. The
-- operations @+@, @-@, @*@, and @\/@ are permitted along with integers and
-- the variables in /x/. The character @^@ must be immediately followed by
-- the (integer) exponent. If any division is not exact, parsing fails.
foreign import ccall "nmod_mpoly.h nmod_mpoly_set_str_pretty"
  nmod_mpoly_set_str_pretty :: Ptr CNModMPoly -> CString -> Ptr (Ptr CChar) -> Ptr CNModMPolyCtx -> IO CInt

-- Basic manipulation ----------------------------------------------------------

-- | /nmod_mpoly_gen/ /A/ /var/ /ctx/ 
--
-- Set /A/ to the variable of index /var/, where \(var = 0\) corresponds to
-- the variable with the most significance with respect to the ordering.
foreign import ccall "nmod_mpoly.h nmod_mpoly_gen"
  nmod_mpoly_gen :: Ptr CNModMPoly -> CLong -> Ptr CNModMPolyCtx -> IO ()

-- | /nmod_mpoly_is_gen/ /A/ /var/ /ctx/ 
--
-- If \(var \ge 0\), return \(1\) if /A/ is equal to the \(var\)-th
-- generator, otherwise return \(0\). If \(var < 0\), return \(1\) if the
-- polynomial is equal to any generator, otherwise return \(0\).
foreign import ccall "nmod_mpoly.h nmod_mpoly_is_gen"
  nmod_mpoly_is_gen :: Ptr CNModMPoly -> CLong -> Ptr CNModMPolyCtx -> IO CInt

-- | /nmod_mpoly_set/ /A/ /B/ /ctx/ 
--
-- Set /A/ to /B/.
foreign import ccall "nmod_mpoly.h nmod_mpoly_set"
  nmod_mpoly_set :: Ptr CNModMPoly -> Ptr CNModMPoly -> Ptr CNModMPolyCtx -> IO ()

-- | /nmod_mpoly_equal/ /A/ /B/ /ctx/ 
--
-- Return \(1\) if /A/ is equal to /B/, else return \(0\).
foreign import ccall "nmod_mpoly.h nmod_mpoly_equal"
  nmod_mpoly_equal :: Ptr CNModMPoly -> Ptr CNModMPoly -> Ptr CNModMPolyCtx -> IO CInt

-- | /nmod_mpoly_swap/ /A/ /B/ /ctx/ 
--
-- Efficiently swap /A/ and /B/.
foreign import ccall "nmod_mpoly.h nmod_mpoly_swap"
  nmod_mpoly_swap :: Ptr CNModMPoly -> Ptr CNModMPoly -> Ptr CNModMPolyCtx -> IO ()

-- Constants -------------------------------------------------------------------

-- | /nmod_mpoly_is_ui/ /A/ /ctx/ 
--
-- Return \(1\) if /A/ is a constant, else return \(0\).
foreign import ccall "nmod_mpoly.h nmod_mpoly_is_ui"
  nmod_mpoly_is_ui :: Ptr CNModMPoly -> Ptr CNModMPolyCtx -> IO CInt

-- | /nmod_mpoly_get_ui/ /A/ /ctx/ 
--
-- Assuming that /A/ is a constant, return this constant. This function
-- throws if /A/ is not a constant.
foreign import ccall "nmod_mpoly.h nmod_mpoly_get_ui"
  nmod_mpoly_get_ui :: Ptr CNModMPoly -> Ptr CNModMPolyCtx -> IO CULong

-- | /nmod_mpoly_set_ui/ /A/ /c/ /ctx/ 
--
-- Set /A/ to the constant /c/.
foreign import ccall "nmod_mpoly.h nmod_mpoly_set_ui"
  nmod_mpoly_set_ui :: Ptr CNModMPoly -> CULong -> Ptr CNModMPolyCtx -> IO ()

-- | /nmod_mpoly_zero/ /A/ /ctx/ 
--
-- Set /A/ to the constant \(0\).
foreign import ccall "nmod_mpoly.h nmod_mpoly_zero"
  nmod_mpoly_zero :: Ptr CNModMPoly -> Ptr CNModMPolyCtx -> IO ()

-- | /nmod_mpoly_one/ /A/ /ctx/ 
--
-- Set /A/ to the constant \(1\).
foreign import ccall "nmod_mpoly.h nmod_mpoly_one"
  nmod_mpoly_one :: Ptr CNModMPoly -> Ptr CNModMPolyCtx -> IO ()

-- | /nmod_mpoly_equal_ui/ /A/ /c/ /ctx/ 
--
-- Return \(1\) if /A/ is equal to the constant /c/, else return \(0\).
foreign import ccall "nmod_mpoly.h nmod_mpoly_equal_ui"
  nmod_mpoly_equal_ui :: Ptr CNModMPoly -> CULong -> Ptr CNModMPolyCtx -> IO CInt

-- | /nmod_mpoly_is_zero/ /A/ /ctx/ 
--
-- Return \(1\) if /A/ is the constant \(0\), else return \(0\).
foreign import ccall "nmod_mpoly.h nmod_mpoly_is_zero"
  nmod_mpoly_is_zero :: Ptr CNModMPoly -> Ptr CNModMPolyCtx -> IO CInt

-- | /nmod_mpoly_is_one/ /A/ /ctx/ 
--
-- Return \(1\) if /A/ is the constant \(1\), else return \(0\).
foreign import ccall "nmod_mpoly.h nmod_mpoly_is_one"
  nmod_mpoly_is_one :: Ptr CNModMPoly -> Ptr CNModMPolyCtx -> IO CInt

-- Degrees ---------------------------------------------------------------------

-- | /nmod_mpoly_degrees_fit_si/ /A/ /ctx/ 
--
-- Return \(1\) if the degrees of /A/ with respect to each variable fit
-- into an @slong@, otherwise return \(0\).
foreign import ccall "nmod_mpoly.h nmod_mpoly_degrees_fit_si"
  nmod_mpoly_degrees_fit_si :: Ptr CNModMPoly -> Ptr CNModMPolyCtx -> IO CInt

-- | /nmod_mpoly_degrees_fmpz/ /degs/ /A/ /ctx/ 
foreign import ccall "nmod_mpoly.h nmod_mpoly_degrees_fmpz"
  nmod_mpoly_degrees_fmpz :: Ptr (Ptr CFmpz) -> Ptr CNModMPoly -> Ptr CNModMPolyCtx -> IO ()
-- | /nmod_mpoly_degrees_si/ /degs/ /A/ /ctx/ 
--
-- Set /degs/ to the degrees of /A/ with respect to each variable. If /A/
-- is zero, all degrees are set to \(-1\).
foreign import ccall "nmod_mpoly.h nmod_mpoly_degrees_si"
  nmod_mpoly_degrees_si :: Ptr CLong -> Ptr CNModMPoly -> Ptr CNModMPolyCtx -> IO ()

-- | /nmod_mpoly_degree_fmpz/ /deg/ /A/ /var/ /ctx/ 
foreign import ccall "nmod_mpoly.h nmod_mpoly_degree_fmpz"
  nmod_mpoly_degree_fmpz :: Ptr CFmpz -> Ptr CNModMPoly -> CLong -> Ptr CNModMPolyCtx -> IO ()
-- | /nmod_mpoly_degree_si/ /A/ /var/ /ctx/ 
--
-- Either return or set /deg/ to the degree of /A/ with respect to the
-- variable of index /var/. If /A/ is zero, the degree is defined to be
-- \(-1\).
foreign import ccall "nmod_mpoly.h nmod_mpoly_degree_si"
  nmod_mpoly_degree_si :: Ptr CNModMPoly -> CLong -> Ptr CNModMPolyCtx -> IO CLong

-- | /nmod_mpoly_total_degree_fits_si/ /A/ /ctx/ 
--
-- Return \(1\) if the total degree of /A/ fits into an @slong@, otherwise
-- return \(0\).
foreign import ccall "nmod_mpoly.h nmod_mpoly_total_degree_fits_si"
  nmod_mpoly_total_degree_fits_si :: Ptr CNModMPoly -> Ptr CNModMPolyCtx -> IO CInt

-- | /nmod_mpoly_total_degree_fmpz/ /tdeg/ /A/ /ctx/ 
foreign import ccall "nmod_mpoly.h nmod_mpoly_total_degree_fmpz"
  nmod_mpoly_total_degree_fmpz :: Ptr CFmpz -> Ptr CNModMPoly -> Ptr CNModMPolyCtx -> IO ()
-- | /nmod_mpoly_total_degree_si/ /A/ /ctx/ 
--
-- Either return or set /tdeg/ to the total degree of /A/. If /A/ is zero,
-- the total degree is defined to be \(-1\).
foreign import ccall "nmod_mpoly.h nmod_mpoly_total_degree_si"
  nmod_mpoly_total_degree_si :: Ptr CNModMPoly -> Ptr CNModMPolyCtx -> IO CLong

-- | /nmod_mpoly_used_vars/ /used/ /A/ /ctx/ 
--
-- For each variable index /i/, set @used[i]@ to nonzero if the variable of
-- index /i/ appears in /A/ and to zero otherwise.
foreign import ccall "nmod_mpoly.h nmod_mpoly_used_vars"
  nmod_mpoly_used_vars :: Ptr CInt -> Ptr CNModMPoly -> Ptr CNModMPolyCtx -> IO ()

-- Coefficients ----------------------------------------------------------------

-- | /nmod_mpoly_get_coeff_ui_monomial/ /A/ /M/ /ctx/ 
--
-- Assuming that /M/ is a monomial, return the coefficient of the
-- corresponding monomial in /A/. This function throws if /M/ is not a
-- monomial.
foreign import ccall "nmod_mpoly.h nmod_mpoly_get_coeff_ui_monomial"
  nmod_mpoly_get_coeff_ui_monomial :: Ptr CNModMPoly -> Ptr CNModMPoly -> Ptr CNModMPolyCtx -> IO CULong

-- | /nmod_mpoly_set_coeff_ui_monomial/ /A/ /c/ /M/ /ctx/ 
--
-- Assuming that /M/ is a monomial, set the coefficient of the
-- corresponding monomial in /A/ to /c/. This function throws if /M/ is not
-- a monomial.
foreign import ccall "nmod_mpoly.h nmod_mpoly_set_coeff_ui_monomial"
  nmod_mpoly_set_coeff_ui_monomial :: Ptr CNModMPoly -> CULong -> Ptr CNModMPoly -> Ptr CNModMPolyCtx -> IO ()

-- | /nmod_mpoly_get_coeff_ui_fmpz/ /A/ /exp/ /ctx/ 
foreign import ccall "nmod_mpoly.h nmod_mpoly_get_coeff_ui_fmpz"
  nmod_mpoly_get_coeff_ui_fmpz :: Ptr CNModMPoly -> Ptr (Ptr CFmpz) -> Ptr CNModMPolyCtx -> IO CULong
-- | /nmod_mpoly_get_coeff_ui_ui/ /A/ /exp/ /ctx/ 
--
-- Return the coefficient of the monomial with exponent /exp/.
foreign import ccall "nmod_mpoly.h nmod_mpoly_get_coeff_ui_ui"
  nmod_mpoly_get_coeff_ui_ui :: Ptr CNModMPoly -> Ptr CULong -> Ptr CNModMPolyCtx -> IO CULong

-- | /nmod_mpoly_set_coeff_ui_fmpz/ /A/ /c/ /exp/ /ctx/ 
foreign import ccall "nmod_mpoly.h nmod_mpoly_set_coeff_ui_fmpz"
  nmod_mpoly_set_coeff_ui_fmpz :: Ptr CNModMPoly -> CULong -> Ptr (Ptr CFmpz) -> Ptr CNModMPolyCtx -> IO ()
-- | /nmod_mpoly_set_coeff_ui_ui/ /A/ /c/ /exp/ /ctx/ 
--
-- Set the coefficient of the monomial with exponent /exp/ to \(c\).
foreign import ccall "nmod_mpoly.h nmod_mpoly_set_coeff_ui_ui"
  nmod_mpoly_set_coeff_ui_ui :: Ptr CNModMPoly -> CULong -> Ptr CULong -> Ptr CNModMPolyCtx -> IO ()

-- | /nmod_mpoly_get_coeff_vars_ui/ /C/ /A/ /vars/ /exps/ /length/ /ctx/ 
--
-- Set /C/ to the coefficient of /A/ with respect to the variables in
-- /vars/ with powers in the corresponding array /exps/. Both /vars/ and
-- /exps/ point to array of length /length/. It is assumed that
-- @0 \< length \\le nvars(A)@ and that the variables in /vars/ are
-- distinct.
foreign import ccall "nmod_mpoly.h nmod_mpoly_get_coeff_vars_ui"
  nmod_mpoly_get_coeff_vars_ui :: Ptr CNModMPoly -> Ptr CNModMPoly -> Ptr CLong -> Ptr CULong -> CLong -> Ptr CNModMPolyCtx -> IO ()

-- Comparison ------------------------------------------------------------------

-- | /nmod_mpoly_cmp/ /A/ /B/ /ctx/ 
--
-- Return \(1\) (resp. \(-1\), or \(0\)) if /A/ is after (resp. before,
-- same as) /B/ in some arbitrary but fixed total ordering of the
-- polynomials. This ordering agrees with the usual ordering of monomials
-- when /A/ and /B/ are both monomials.
foreign import ccall "nmod_mpoly.h nmod_mpoly_cmp"
  nmod_mpoly_cmp :: Ptr CNModMPoly -> Ptr CNModMPoly -> Ptr CNModMPolyCtx -> IO CInt

-- Container operations --------------------------------------------------------

-- | /nmod_mpoly_term_coeff_ref/ /A/ /i/ /ctx/ 
--
-- Return a reference to the coefficient of index /i/ of /A/.
foreign import ccall "nmod_mpoly.h nmod_mpoly_term_coeff_ref"
  nmod_mpoly_term_coeff_ref :: Ptr CNModMPoly -> CLong -> Ptr CNModMPolyCtx -> IO (Ptr CMpLimb)

-- | /nmod_mpoly_is_canonical/ /A/ /ctx/ 
--
-- Return \(1\) if /A/ is in canonical form. Otherwise, return \(0\). To be
-- in canonical form, all of the terms must have nonzero coefficients, and
-- the terms must be sorted from greatest to least.
foreign import ccall "nmod_mpoly.h nmod_mpoly_is_canonical"
  nmod_mpoly_is_canonical :: Ptr CNModMPoly -> Ptr CNModMPolyCtx -> IO CInt

-- | /nmod_mpoly_length/ /A/ /ctx/ 
--
-- Return the number of terms in /A/. If the polynomial is in canonical
-- form, this will be the number of nonzero coefficients.
foreign import ccall "nmod_mpoly.h nmod_mpoly_length"
  nmod_mpoly_length :: Ptr CNModMPoly -> Ptr CNModMPolyCtx -> IO CLong

-- | /nmod_mpoly_resize/ /A/ /new_length/ /ctx/ 
--
-- Set the length of /A/ to @new_length@. Terms are either deleted from the
-- end, or new zero terms are appended.
foreign import ccall "nmod_mpoly.h nmod_mpoly_resize"
  nmod_mpoly_resize :: Ptr CNModMPoly -> CLong -> Ptr CNModMPolyCtx -> IO ()

-- | /nmod_mpoly_get_term_coeff_ui/ /A/ /i/ /ctx/ 
--
-- Return the coefficient of the term of index /i/.
foreign import ccall "nmod_mpoly.h nmod_mpoly_get_term_coeff_ui"
  nmod_mpoly_get_term_coeff_ui :: Ptr CNModMPoly -> CLong -> Ptr CNModMPolyCtx -> IO CULong

-- | /nmod_mpoly_set_term_coeff_ui/ /A/ /i/ /c/ /ctx/ 
--
-- Set the coefficient of the term of index /i/ to /c/.
foreign import ccall "nmod_mpoly.h nmod_mpoly_set_term_coeff_ui"
  nmod_mpoly_set_term_coeff_ui :: Ptr CNModMPoly -> CLong -> CULong -> Ptr CNModMPolyCtx -> IO ()

-- | /nmod_mpoly_term_exp_fits_si/ /A/ /i/ /ctx/ 
foreign import ccall "nmod_mpoly.h nmod_mpoly_term_exp_fits_si"
  nmod_mpoly_term_exp_fits_si :: Ptr CNModMPoly -> CLong -> Ptr CNModMPolyCtx -> IO CInt
-- | /nmod_mpoly_term_exp_fits_ui/ /A/ /i/ /ctx/ 
--
-- Return \(1\) if all entries of the exponent vector of the term of index
-- /i/ fit into an @slong@ (resp. a @ulong@). Otherwise, return \(0\).
foreign import ccall "nmod_mpoly.h nmod_mpoly_term_exp_fits_ui"
  nmod_mpoly_term_exp_fits_ui :: Ptr CNModMPoly -> CLong -> Ptr CNModMPolyCtx -> IO CInt

-- | /nmod_mpoly_get_term_exp_fmpz/ /exp/ /A/ /i/ /ctx/ 
foreign import ccall "nmod_mpoly.h nmod_mpoly_get_term_exp_fmpz"
  nmod_mpoly_get_term_exp_fmpz :: Ptr (Ptr CFmpz) -> Ptr CNModMPoly -> CLong -> Ptr CNModMPolyCtx -> IO ()
-- | /nmod_mpoly_get_term_exp_ui/ /exp/ /A/ /i/ /ctx/ 
--
foreign import ccall "nmod_mpoly.h nmod_mpoly_get_term_exp_ui"
  nmod_mpoly_get_term_exp_ui :: Ptr CULong -> Ptr CNModMPoly -> CLong -> Ptr CNModMPolyCtx -> IO ()

-- | /nmod_mpoly_get_term_exp_si/ /exp/ /A/ /i/ /ctx/ 
--
-- Set /exp/ to the exponent vector of the term of index /i/. The @_ui@
-- (resp. @_si@) version throws if any entry does not fit into a @ulong@
-- (resp. @slong@).
foreign import ccall "nmod_mpoly.h nmod_mpoly_get_term_exp_si"
  nmod_mpoly_get_term_exp_si :: Ptr CLong -> Ptr CNModMPoly -> CLong -> Ptr CNModMPolyCtx -> IO ()

-- | /nmod_mpoly_get_term_var_exp_ui/ /A/ /i/ /var/ /ctx/ 
foreign import ccall "nmod_mpoly.h nmod_mpoly_get_term_var_exp_ui"
  nmod_mpoly_get_term_var_exp_ui :: Ptr CNModMPoly -> CLong -> CLong -> Ptr CNModMPolyCtx -> IO CULong
-- | /nmod_mpoly_get_term_var_exp_si/ /A/ /i/ /var/ /ctx/ 
--
-- Return the exponent of the variable /var/ of the term of index /i/. This
-- function throws if the exponent does not fit into a @ulong@ (resp.
-- @slong@).
foreign import ccall "nmod_mpoly.h nmod_mpoly_get_term_var_exp_si"
  nmod_mpoly_get_term_var_exp_si :: Ptr CNModMPoly -> CLong -> CLong -> Ptr CNModMPolyCtx -> IO CLong

-- | /nmod_mpoly_set_term_exp_fmpz/ /A/ /i/ /exp/ /ctx/ 
foreign import ccall "nmod_mpoly.h nmod_mpoly_set_term_exp_fmpz"
  nmod_mpoly_set_term_exp_fmpz :: Ptr CNModMPoly -> CLong -> Ptr (Ptr CFmpz) -> Ptr CNModMPolyCtx -> IO ()
-- | /nmod_mpoly_set_term_exp_ui/ /A/ /i/ /exp/ /ctx/ 
--
-- Set the exponent of the term of index /i/ to /exp/.
foreign import ccall "nmod_mpoly.h nmod_mpoly_set_term_exp_ui"
  nmod_mpoly_set_term_exp_ui :: Ptr CNModMPoly -> CLong -> Ptr CULong -> Ptr CNModMPolyCtx -> IO ()

-- | /nmod_mpoly_get_term/ /M/ /A/ /i/ /ctx/ 
--
-- Set /M/ to the term of index /i/ in /A/.
foreign import ccall "nmod_mpoly.h nmod_mpoly_get_term"
  nmod_mpoly_get_term :: Ptr CNModMPoly -> Ptr CNModMPoly -> CLong -> Ptr CNModMPolyCtx -> IO ()

-- | /nmod_mpoly_get_term_monomial/ /M/ /A/ /i/ /ctx/ 
--
-- Set /M/ to the monomial of the term of index /i/ in /A/. The coefficient
-- of /M/ will be one.
foreign import ccall "nmod_mpoly.h nmod_mpoly_get_term_monomial"
  nmod_mpoly_get_term_monomial :: Ptr CNModMPoly -> Ptr CNModMPoly -> CLong -> Ptr CNModMPolyCtx -> IO ()

-- | /nmod_mpoly_push_term_ui_fmpz/ /A/ /c/ /exp/ /ctx/ 
foreign import ccall "nmod_mpoly.h nmod_mpoly_push_term_ui_fmpz"
  nmod_mpoly_push_term_ui_fmpz :: Ptr CNModMPoly -> CULong -> Ptr (Ptr CFmpz) -> Ptr CNModMPolyCtx -> IO ()
-- | /nmod_mpoly_push_term_ui_ui/ /A/ /c/ /exp/ /ctx/ 
--
-- Append a term to /A/ with coefficient /c/ and exponent vector /exp/.
-- This function runs in constant average time.
foreign import ccall "nmod_mpoly.h nmod_mpoly_push_term_ui_ui"
  nmod_mpoly_push_term_ui_ui :: Ptr CNModMPoly -> CULong -> Ptr CULong -> Ptr CNModMPolyCtx -> IO ()

-- | /nmod_mpoly_sort_terms/ /A/ /ctx/ 
--
-- Sort the terms of /A/ into the canonical ordering dictated by the
-- ordering in /ctx/. This function simply reorders the terms: It does not
-- combine like terms, nor does it delete terms with coefficient zero. This
-- function runs in linear time in the bit size of /A/.
foreign import ccall "nmod_mpoly.h nmod_mpoly_sort_terms"
  nmod_mpoly_sort_terms :: Ptr CNModMPoly -> Ptr CNModMPolyCtx -> IO ()

-- | /nmod_mpoly_combine_like_terms/ /A/ /ctx/ 
--
-- Combine adjacent like terms in /A/ and delete terms with coefficient
-- zero. If the terms of /A/ were sorted to begin with, the result will be
-- in canonical form. This function runs in linear time in the bit size of
-- /A/.
foreign import ccall "nmod_mpoly.h nmod_mpoly_combine_like_terms"
  nmod_mpoly_combine_like_terms :: Ptr CNModMPoly -> Ptr CNModMPolyCtx -> IO ()

-- | /nmod_mpoly_reverse/ /A/ /B/ /ctx/ 
--
-- Set /A/ to the reversal of /B/.
foreign import ccall "nmod_mpoly.h nmod_mpoly_reverse"
  nmod_mpoly_reverse :: Ptr CNModMPoly -> Ptr CNModMPoly -> Ptr CNModMPolyCtx -> IO ()

-- Random generation -----------------------------------------------------------

-- | /nmod_mpoly_randtest_bound/ /A/ /state/ /length/ /exp_bound/ /ctx/ 
--
-- Generate a random polynomial with length up to /length/ and exponents in
-- the range @[0, exp_bound - 1]@. The exponents of each variable are
-- generated by calls to @n_randint(state, exp_bound)@.
foreign import ccall "nmod_mpoly.h nmod_mpoly_randtest_bound"
  nmod_mpoly_randtest_bound :: Ptr CNModMPoly -> Ptr CFRandState -> CLong -> CULong -> Ptr CNModMPolyCtx -> IO ()

-- | /nmod_mpoly_randtest_bounds/ /A/ /state/ /length/ /exp_bounds/ /ctx/ 
--
-- Generate a random polynomial with length up to /length/ and exponents in
-- the range @[0, exp_bounds[i] - 1]@. The exponents of the variable of
-- index /i/ are generated by calls to @n_randint(state, exp_bounds[i])@.
foreign import ccall "nmod_mpoly.h nmod_mpoly_randtest_bounds"
  nmod_mpoly_randtest_bounds :: Ptr CNModMPoly -> Ptr CFRandState -> CLong -> CULong -> Ptr CNModMPolyCtx -> IO ()

-- | /nmod_mpoly_randtest_bits/ /A/ /state/ /length/ /exp_bits/ /ctx/ 
--
-- Generate a random polynomial with length up to /length/ and exponents
-- whose packed form does not exceed the given bit count.
foreign import ccall "nmod_mpoly.h nmod_mpoly_randtest_bits"
  nmod_mpoly_randtest_bits :: Ptr CNModMPoly -> Ptr CFRandState -> CLong -> CMpLimb -> Ptr CNModMPolyCtx -> IO ()

-- Addition\/Subtraction -------------------------------------------------------

-- | /nmod_mpoly_add_ui/ /A/ /B/ /c/ /ctx/ 
--
-- Set /A/ to \(B + c\).
foreign import ccall "nmod_mpoly.h nmod_mpoly_add_ui"
  nmod_mpoly_add_ui :: Ptr CNModMPoly -> Ptr CNModMPoly -> CULong -> Ptr CNModMPolyCtx -> IO ()

-- | /nmod_mpoly_sub_ui/ /A/ /B/ /c/ /ctx/ 
--
-- Set /A/ to \(B - c\).
foreign import ccall "nmod_mpoly.h nmod_mpoly_sub_ui"
  nmod_mpoly_sub_ui :: Ptr CNModMPoly -> Ptr CNModMPoly -> CULong -> Ptr CNModMPolyCtx -> IO ()

-- | /nmod_mpoly_add/ /A/ /B/ /C/ /ctx/ 
--
-- Set /A/ to \(B + C\).
foreign import ccall "nmod_mpoly.h nmod_mpoly_add"
  nmod_mpoly_add :: Ptr CNModMPoly -> Ptr CNModMPoly -> Ptr CNModMPoly -> Ptr CNModMPolyCtx -> IO ()

-- | /nmod_mpoly_sub/ /A/ /B/ /C/ /ctx/ 
--
-- Set /A/ to \(B - C\).
foreign import ccall "nmod_mpoly.h nmod_mpoly_sub"
  nmod_mpoly_sub :: Ptr CNModMPoly -> Ptr CNModMPoly -> Ptr CNModMPoly -> Ptr CNModMPolyCtx -> IO ()

-- Scalar operations -----------------------------------------------------------

-- | /nmod_mpoly_neg/ /A/ /B/ /ctx/ 
--
-- Set /A/ to \(-B\).
foreign import ccall "nmod_mpoly.h nmod_mpoly_neg"
  nmod_mpoly_neg :: Ptr CNModMPoly -> Ptr CNModMPoly -> Ptr CNModMPolyCtx -> IO ()

-- | /nmod_mpoly_scalar_mul_ui/ /A/ /B/ /c/ /ctx/ 
--
-- Set /A/ to \(B \times c\).
foreign import ccall "nmod_mpoly.h nmod_mpoly_scalar_mul_ui"
  nmod_mpoly_scalar_mul_ui :: Ptr CNModMPoly -> Ptr CNModMPoly -> CULong -> Ptr CNModMPolyCtx -> IO ()

-- | /nmod_mpoly_make_monic/ /A/ /B/ /ctx/ 
--
-- Set /A/ to /B/ divided by the leading coefficient of /B/. This throws if
-- /B/ is zero or the leading coefficient is not invertible.
foreign import ccall "nmod_mpoly.h nmod_mpoly_make_monic"
  nmod_mpoly_make_monic :: Ptr CNModMPoly -> Ptr CNModMPoly -> Ptr CNModMPolyCtx -> IO ()

-- Differentiation -------------------------------------------------------------

-- | /nmod_mpoly_derivative/ /A/ /B/ /var/ /ctx/ 
--
-- Set /A/ to the derivative of /B/ with respect to the variable of index
-- /var/.
foreign import ccall "nmod_mpoly.h nmod_mpoly_derivative"
  nmod_mpoly_derivative :: Ptr CNModMPoly -> Ptr CNModMPoly -> CLong -> Ptr CNModMPolyCtx -> IO ()

-- Evaluation ------------------------------------------------------------------

-- | /nmod_mpoly_evaluate_all_ui/ /A/ /vals/ /ctx/ 
--
-- Return the evaluation of /A/ where the variables are replaced by the
-- corresponding elements of the array /vals/.
foreign import ccall "nmod_mpoly.h nmod_mpoly_evaluate_all_ui"
  nmod_mpoly_evaluate_all_ui :: Ptr CNModMPoly -> Ptr CULong -> Ptr CNModMPolyCtx -> IO CULong

-- | /nmod_mpoly_evaluate_one_ui/ /A/ /B/ /var/ /val/ /ctx/ 
--
-- Set /A/ to the evaluation of /B/ where the variable of index /var/ is
-- replaced by /val/.
foreign import ccall "nmod_mpoly.h nmod_mpoly_evaluate_one_ui"
  nmod_mpoly_evaluate_one_ui :: Ptr CNModMPoly -> Ptr CNModMPoly -> CULong -> CULong -> Ptr CNModMPolyCtx -> IO ()

-- | /nmod_mpoly_compose_nmod_poly/ /A/ /B/ /C/ /ctx/ 
--
-- Set /A/ to the evaluation of /B/ where the variables are replaced by the
-- corresponding elements of the array /C/. The context object of /B/ is
-- /ctxB/. Return \(1\) for success and \(0\) for failure.
foreign import ccall "nmod_mpoly.h nmod_mpoly_compose_nmod_poly"
  nmod_mpoly_compose_nmod_poly :: Ptr CNModPoly -> Ptr CNModMPoly -> Ptr (Ptr (Ptr CNModPoly)) -> Ptr CNModMPolyCtx -> IO CInt

-- | /nmod_mpoly_compose_nmod_mpoly_geobucket/ /A/ /B/ /C/ /ctxB/ /ctxAC/ 
foreign import ccall "nmod_mpoly.h nmod_mpoly_compose_nmod_mpoly_geobucket"
  nmod_mpoly_compose_nmod_mpoly_geobucket :: Ptr CNModMPoly -> Ptr CNModMPoly -> Ptr (Ptr (Ptr CNModMPoly)) -> Ptr CNModMPolyCtx -> Ptr CNModMPolyCtx -> IO CInt
-- | /nmod_mpoly_compose_nmod_mpoly_horner/ /A/ /B/ /C/ /ctxB/ /ctxAC/ 
foreign import ccall "nmod_mpoly.h nmod_mpoly_compose_nmod_mpoly_horner"
  nmod_mpoly_compose_nmod_mpoly_horner :: Ptr CNModMPoly -> Ptr CNModMPoly -> Ptr (Ptr (Ptr CNModMPoly)) -> Ptr CNModMPolyCtx -> Ptr CNModMPolyCtx -> IO CInt
-- | /nmod_mpoly_compose_nmod_mpoly/ /A/ /B/ /C/ /ctxB/ /ctxAC/ 
--
-- Set /A/ to the evaluation of /B/ where the variables are replaced by the
-- corresponding elements of the array /C/. Both /A/ and the elements of
-- /C/ have context object /ctxAC/, while /B/ has context object /ctxB/.
-- Neither of /A/ and /B/ is allowed to alias any other polynomial. Return
-- \(1\) for success and \(0\) for failure. The main method attempts to
-- perform the calculation using matrices and chooses heuristically between
-- the @geobucket@ and @horner@ methods if needed.
foreign import ccall "nmod_mpoly.h nmod_mpoly_compose_nmod_mpoly"
  nmod_mpoly_compose_nmod_mpoly :: Ptr CNModMPoly -> Ptr CNModMPoly -> Ptr (Ptr (Ptr CNModMPoly)) -> Ptr CNModMPolyCtx -> Ptr CNModMPolyCtx -> IO CInt

-- | /nmod_mpoly_compose_nmod_mpoly_gen/ /A/ /B/ /c/ /ctxB/ /ctxAC/ 
--
-- Set /A/ to the evaluation of /B/ where the variable of index /i/ in
-- /ctxB/ is replaced by the variable of index @c[i]@ in /ctxAC/. The
-- length of the array /C/ is the number of variables in /ctxB/. If any
-- @c[i]@ is negative, the corresponding variable of /B/ is replaced by
-- zero. Otherwise, it is expected that @c[i]@ is less than the number of
-- variables in /ctxAC/.
foreign import ccall "nmod_mpoly.h nmod_mpoly_compose_nmod_mpoly_gen"
  nmod_mpoly_compose_nmod_mpoly_gen :: Ptr CNModMPoly -> Ptr CNModMPoly -> Ptr CLong -> Ptr CNModMPolyCtx -> Ptr CNModMPolyCtx -> IO ()

-- Multiplication --------------------------------------------------------------

-- | /nmod_mpoly_mul/ /A/ /B/ /C/ /ctx/ 
--
-- Set /A/ to \(B \times C\).
foreign import ccall "nmod_mpoly.h nmod_mpoly_mul"
  nmod_mpoly_mul :: Ptr CNModMPoly -> Ptr CNModMPoly -> Ptr CNModMPoly -> Ptr CNModMPolyCtx -> IO ()

-- | /nmod_mpoly_mul_johnson/ /A/ /B/ /C/ /ctx/ 
foreign import ccall "nmod_mpoly.h nmod_mpoly_mul_johnson"
  nmod_mpoly_mul_johnson :: Ptr CNModMPoly -> Ptr CNModMPoly -> Ptr CNModMPoly -> Ptr CNModMPolyCtx -> IO ()
-- | /nmod_mpoly_mul_heap_threaded/ /A/ /B/ /C/ /ctx/ 
--
-- Set /A/ to \(B \times C\) using Johnson\'s heap-based method. The first
-- version always uses one thread.
foreign import ccall "nmod_mpoly.h nmod_mpoly_mul_heap_threaded"
  nmod_mpoly_mul_heap_threaded :: Ptr CNModMPoly -> Ptr CNModMPoly -> Ptr CNModMPoly -> Ptr CNModMPolyCtx -> IO ()

-- | /nmod_mpoly_mul_array/ /A/ /B/ /C/ /ctx/ 
foreign import ccall "nmod_mpoly.h nmod_mpoly_mul_array"
  nmod_mpoly_mul_array :: Ptr CNModMPoly -> Ptr CNModMPoly -> Ptr CNModMPoly -> Ptr CNModMPolyCtx -> IO CInt
-- | /nmod_mpoly_mul_array_threaded/ /A/ /B/ /C/ /ctx/ 
--
-- Try to set /A/ to \(B \times C\) using arrays. If the return is \(0\),
-- the operation was unsuccessful. Otherwise, it was successful, and the
-- return is \(1\). The first version always uses one thread.
foreign import ccall "nmod_mpoly.h nmod_mpoly_mul_array_threaded"
  nmod_mpoly_mul_array_threaded :: Ptr CNModMPoly -> Ptr CNModMPoly -> Ptr CNModMPoly -> Ptr CNModMPolyCtx -> IO CInt

-- | /nmod_mpoly_mul_dense/ /A/ /B/ /C/ /ctx/ 
--
-- Try to set /A/ to \(B \times C\) using univariate arithmetic. If the
-- return is \(0\), the operation was unsuccessful. Otherwise, it was
-- successful and the return is \(1\).
foreign import ccall "nmod_mpoly.h nmod_mpoly_mul_dense"
  nmod_mpoly_mul_dense :: Ptr CNModMPoly -> Ptr CNModMPoly -> Ptr CNModMPoly -> Ptr CNModMPolyCtx -> IO CInt

-- Powering --------------------------------------------------------------------




-- | /nmod_mpoly_pow_fmpz/ /A/ /B/ /k/ /ctx/ 
--
-- Set /A/ to /B/ raised to the /k/-th power. Return \(1\) for success and
-- \(0\) for failure.
foreign import ccall "nmod_mpoly.h nmod_mpoly_pow_fmpz"
  nmod_mpoly_pow_fmpz :: Ptr CNModMPoly -> Ptr CNModMPoly -> Ptr CFmpz -> Ptr CNModMPolyCtx -> IO CInt

-- | /nmod_mpoly_pow_ui/ /A/ /B/ /k/ /ctx/ 
--
-- Set /A/ to /B/ raised to the /k/-th power. Return \(1\) for success and
-- \(0\) for failure.
foreign import ccall "nmod_mpoly.h nmod_mpoly_pow_ui"
  nmod_mpoly_pow_ui :: Ptr CNModMPoly -> Ptr CNModMPoly -> CULong -> Ptr CNModMPolyCtx -> IO CInt

-- Division --------------------------------------------------------------------

-- The division functions assume that the modulus is prime.
--
-- | /nmod_mpoly_divides/ /Q/ /A/ /B/ /ctx/ 
--
-- If /A/ is divisible by /B/, set /Q/ to the exact quotient and return
-- \(1\). Otherwise, set /Q/ to zero and return \(0\). Note that the
-- function @nmod_mpoly_div@ below may be faster if the quotient is known
-- to be exact.
foreign import ccall "nmod_mpoly.h nmod_mpoly_divides"
  nmod_mpoly_divides :: Ptr CNModMPoly -> Ptr CNModMPoly -> Ptr CNModMPoly -> Ptr CNModMPolyCtx -> IO CInt

-- | /nmod_mpoly_div/ /Q/ /A/ /B/ /ctx/ 
--
-- Set /Q/ to the quotient of /A/ by /B/, discarding the remainder.
foreign import ccall "nmod_mpoly.h nmod_mpoly_div"
  nmod_mpoly_div :: Ptr CNModMPoly -> Ptr CNModMPoly -> Ptr CNModMPoly -> Ptr CNModMPolyCtx -> IO ()

-- | /nmod_mpoly_divrem/ /Q/ /R/ /A/ /B/ /ctx/ 
--
-- Set /Q/ and /R/ to the quotient and remainder of /A/ divided by /B/.
foreign import ccall "nmod_mpoly.h nmod_mpoly_divrem"
  nmod_mpoly_divrem :: Ptr CNModMPoly -> Ptr CNModMPoly -> Ptr CNModMPoly -> Ptr CNModMPoly -> Ptr CNModMPolyCtx -> IO ()

-- | /nmod_mpoly_divrem_ideal/ /Q/ /R/ /A/ /B/ /len/ /ctx/ 
--
-- This function is as per @nmod_mpoly_divrem@ except that it takes an
-- array of divisor polynomials /B/ and it returns an array of quotient
-- polynomials /Q/. The number of divisor (and hence quotient) polynomials,
-- is given by /len/.
foreign import ccall "nmod_mpoly.h nmod_mpoly_divrem_ideal"
  nmod_mpoly_divrem_ideal :: Ptr (Ptr (Ptr CNModMPoly)) -> Ptr CNModMPoly -> Ptr CNModMPoly -> Ptr (Ptr (Ptr CNModMPoly)) -> CLong -> Ptr CNModMPolyCtx -> IO ()

-- | /nmod_mpoly_divides_dense/ /Q/ /A/ /B/ /ctx/ 
--
-- Try to do the operation of @nmod_mpoly_divides@ using univariate
-- arithmetic. If the return is \(-1\), the operation was unsuccessful.
-- Otherwise, it was successful and the return is \(0\) or \(1\).
foreign import ccall "nmod_mpoly.h nmod_mpoly_divides_dense"
  nmod_mpoly_divides_dense :: Ptr CNModMPoly -> Ptr CNModMPoly -> Ptr CNModMPoly -> Ptr CNModMPolyCtx -> IO CInt

-- | /nmod_mpoly_divides_monagan_pearce/ /Q/ /A/ /B/ /ctx/ 
--
-- Do the operation of @nmod_mpoly_divides@ using the algorithm of Michael
-- Monagan and Roman Pearce.
foreign import ccall "nmod_mpoly.h nmod_mpoly_divides_monagan_pearce"
  nmod_mpoly_divides_monagan_pearce :: Ptr CNModMPoly -> Ptr CNModMPoly -> Ptr CNModMPoly -> Ptr CNModMPolyCtx -> IO CInt

-- | /nmod_mpoly_divides_heap_threaded/ /Q/ /A/ /B/ /ctx/ 
--
-- Do the operation of @nmod_mpoly_divides@ using a heap and multiple
-- threads. This function should only be called once @global_thread_pool@
-- has been initialized.
foreign import ccall "nmod_mpoly.h nmod_mpoly_divides_heap_threaded"
  nmod_mpoly_divides_heap_threaded :: Ptr CNModMPoly -> Ptr CNModMPoly -> Ptr CNModMPoly -> Ptr CNModMPolyCtx -> IO CInt

-- Greatest Common Divisor -----------------------------------------------------

-- The greatest common divisor functions assume that the modulus is prime.
--
-- | /nmod_mpoly_term_content/ /M/ /A/ /ctx/ 
--
-- Set /M/ to the GCD of the terms of /A/. If /A/ is zero, /M/ will be
-- zero. Otherwise, /M/ will be a monomial with coefficient one.
foreign import ccall "nmod_mpoly.h nmod_mpoly_term_content"
  nmod_mpoly_term_content :: Ptr CNModMPoly -> Ptr CNModMPoly -> Ptr CNModMPolyCtx -> IO ()

-- | /nmod_mpoly_content_vars/ /g/ /A/ /vars/ /vars_length/ /ctx/ 
--
-- Set /g/ to the GCD of the coefficients of /A/ when viewed as a
-- polynomial in the variables /vars/. Return \(1\) for success and \(0\)
-- for failure. Upon success, /g/ will be independent of the variables
-- /vars/.
foreign import ccall "nmod_mpoly.h nmod_mpoly_content_vars"
  nmod_mpoly_content_vars :: Ptr CNModMPoly -> Ptr CNModMPoly -> Ptr CLong -> CLong -> Ptr CNModMPolyCtx -> IO CInt

-- | /nmod_mpoly_gcd/ /G/ /A/ /B/ /ctx/ 
--
-- Try to set /G/ to the monic GCD of /A/ and /B/. The GCD of zero and zero
-- is defined to be zero. If the return is \(1\) the function was
-- successful. Otherwise the return is \(0\) and /G/ is left untouched.
foreign import ccall "nmod_mpoly.h nmod_mpoly_gcd"
  nmod_mpoly_gcd :: Ptr CNModMPoly -> Ptr CNModMPoly -> Ptr CNModMPoly -> Ptr CNModMPolyCtx -> IO CInt

-- | /nmod_mpoly_gcd_cofactors/ /G/ /Abar/ /Bbar/ /A/ /B/ /ctx/ 
--
-- Do the operation of @nmod_mpoly_gcd@ and also compute \(Abar = A/G\) and
-- \(Bbar = B/G\) if successful.
foreign import ccall "nmod_mpoly.h nmod_mpoly_gcd_cofactors"
  nmod_mpoly_gcd_cofactors :: Ptr CNModMPoly -> Ptr CNModMPoly -> Ptr CNModMPoly -> Ptr CNModMPoly -> Ptr CNModMPoly -> Ptr CNModMPolyCtx -> IO CInt

-- | /nmod_mpoly_gcd_brown/ /G/ /A/ /B/ /ctx/ 
foreign import ccall "nmod_mpoly.h nmod_mpoly_gcd_brown"
  nmod_mpoly_gcd_brown :: Ptr CNModMPoly -> Ptr CNModMPoly -> Ptr CNModMPoly -> Ptr CNModMPolyCtx -> IO CInt
-- | /nmod_mpoly_gcd_hensel/ /G/ /A/ /B/ /ctx/ 
foreign import ccall "nmod_mpoly.h nmod_mpoly_gcd_hensel"
  nmod_mpoly_gcd_hensel :: Ptr CNModMPoly -> Ptr CNModMPoly -> Ptr CNModMPoly -> Ptr CNModMPolyCtx -> IO CInt
-- | /nmod_mpoly_gcd_zippel/ /G/ /A/ /B/ /ctx/ 
--
-- Try to set /G/ to the GCD of /A/ and /B/ using various algorithms.
foreign import ccall "nmod_mpoly.h nmod_mpoly_gcd_zippel"
  nmod_mpoly_gcd_zippel :: Ptr CNModMPoly -> Ptr CNModMPoly -> Ptr CNModMPoly -> Ptr CNModMPolyCtx -> IO CInt

-- | /nmod_mpoly_resultant/ /R/ /A/ /B/ /var/ /ctx/ 
--
-- Try to set /R/ to the resultant of /A/ and /B/ with respect to the
-- variable of index /var/.
foreign import ccall "nmod_mpoly.h nmod_mpoly_resultant"
  nmod_mpoly_resultant :: Ptr CNModMPoly -> Ptr CNModMPoly -> Ptr CNModMPoly -> CLong -> Ptr CNModMPolyCtx -> IO CInt

-- | /nmod_mpoly_discriminant/ /D/ /A/ /var/ /ctx/ 
--
-- Try to set /D/ to the discriminant of /A/ with respect to the variable
-- of index /var/.
foreign import ccall "nmod_mpoly.h nmod_mpoly_discriminant"
  nmod_mpoly_discriminant :: Ptr CNModMPoly -> Ptr CNModMPoly -> CLong -> Ptr CNModMPolyCtx -> IO CInt

-- Square Root -----------------------------------------------------------------

-- The square root functions assume that the modulus is prime for correct
-- operation.
--
-- | /nmod_mpoly_sqrt/ /Q/ /A/ /ctx/ 
--
-- If \(Q^2=A\) has a solution, set /Q/ to a solution and return \(1\),
-- otherwise return \(0\) and set /Q/ to zero.
foreign import ccall "nmod_mpoly.h nmod_mpoly_sqrt"
  nmod_mpoly_sqrt :: Ptr CNModMPoly -> Ptr CNModMPoly -> Ptr CNModMPolyCtx -> IO CInt

-- | /nmod_mpoly_is_square/ /A/ /ctx/ 
--
-- Return \(1\) if /A/ is a perfect square, otherwise return \(0\).
foreign import ccall "nmod_mpoly.h nmod_mpoly_is_square"
  nmod_mpoly_is_square :: Ptr CNModMPoly -> Ptr CNModMPolyCtx -> IO CInt

-- | /nmod_mpoly_quadratic_root/ /Q/ /A/ /B/ /ctx/ 
--
-- If \(Q^2+AQ=B\) has a solution, set /Q/ to a solution and return \(1\),
-- otherwise return \(0\).
foreign import ccall "nmod_mpoly.h nmod_mpoly_quadratic_root"
  nmod_mpoly_quadratic_root :: Ptr CNModMPoly -> Ptr CNModMPoly -> Ptr CNModMPoly -> Ptr CNModMPolyCtx -> IO CInt

-- Univariate Functions --------------------------------------------------------

-- | /nmod_mpoly_univar_init/ /A/ /ctx/ 
--
-- Initialize /A/.
foreign import ccall "nmod_mpoly.h nmod_mpoly_univar_init"
  nmod_mpoly_univar_init :: Ptr CNModMPolyUnivar -> Ptr CNModMPolyCtx -> IO ()

-- | /nmod_mpoly_univar_clear/ /A/ /ctx/ 
--
-- Clear /A/.
foreign import ccall "nmod_mpoly.h nmod_mpoly_univar_clear"
  nmod_mpoly_univar_clear :: Ptr CNModMPolyUnivar -> Ptr CNModMPolyCtx -> IO ()

foreign import ccall "nmod_mpoly.h &nmod_mpoly_univar_clear"
  p_nmod_mpoly_univar_clear :: FunPtr (Ptr CNModMPolyUnivar -> Ptr CNModMPolyCtx -> IO ())

-- | /nmod_mpoly_univar_swap/ /A/ /B/ /ctx/ 
--
-- Swap /A/ and /B/.
foreign import ccall "nmod_mpoly.h nmod_mpoly_univar_swap"
  nmod_mpoly_univar_swap :: Ptr CNModMPolyUnivar -> Ptr CNModMPolyUnivar -> Ptr CNModMPolyCtx -> IO ()

-- | /nmod_mpoly_to_univar/ /A/ /B/ /var/ /ctx/ 
--
-- Set /A/ to a univariate form of /B/ by pulling out the variable of index
-- /var/. The coefficients of /A/ will still belong to the content /ctx/
-- but will not depend on the variable of index /var/.
foreign import ccall "nmod_mpoly.h nmod_mpoly_to_univar"
  nmod_mpoly_to_univar :: Ptr CNModMPolyUnivar -> Ptr CNModMPoly -> CLong -> Ptr CNModMPolyCtx -> IO ()

-- | /nmod_mpoly_from_univar/ /A/ /B/ /var/ /ctx/ 
--
-- Set /A/ to the normal form of /B/ by putting in the variable of index
-- /var/. This function is undefined if the coefficients of /B/ depend on
-- the variable of index /var/.
foreign import ccall "nmod_mpoly.h nmod_mpoly_from_univar"
  nmod_mpoly_from_univar :: Ptr CNModMPoly -> Ptr CNModMPolyUnivar -> CLong -> Ptr CNModMPolyCtx -> IO ()

-- | /nmod_mpoly_univar_degree_fits_si/ /A/ /ctx/ 
--
-- Return \(1\) if the degree of /A/ with respect to the main variable fits
-- an @slong@. Otherwise, return \(0\).
foreign import ccall "nmod_mpoly.h nmod_mpoly_univar_degree_fits_si"
  nmod_mpoly_univar_degree_fits_si :: Ptr CNModMPolyUnivar -> Ptr CNModMPolyCtx -> IO CInt

-- | /nmod_mpoly_univar_length/ /A/ /ctx/ 
--
-- Return the number of terms in /A/ with respect to the main variable.
foreign import ccall "nmod_mpoly.h nmod_mpoly_univar_length"
  nmod_mpoly_univar_length :: Ptr CNModMPolyUnivar -> Ptr CNModMPolyCtx -> IO CLong

-- | /nmod_mpoly_univar_get_term_exp_si/ /A/ /i/ /ctx/ 
--
-- Return the exponent of the term of index /i/ of /A/.
foreign import ccall "nmod_mpoly.h nmod_mpoly_univar_get_term_exp_si"
  nmod_mpoly_univar_get_term_exp_si :: Ptr CNModMPolyUnivar -> CLong -> Ptr CNModMPolyCtx -> IO CLong

-- | /nmod_mpoly_univar_get_term_coeff/ /c/ /A/ /i/ /ctx/ 
foreign import ccall "nmod_mpoly.h nmod_mpoly_univar_get_term_coeff"
  nmod_mpoly_univar_get_term_coeff :: Ptr CNModMPoly -> Ptr CNModMPolyUnivar -> CLong -> Ptr CNModMPolyCtx -> IO ()
-- | /nmod_mpoly_univar_swap_term_coeff/ /c/ /A/ /i/ /ctx/ 
--
-- Set (resp. swap) /c/ to (resp. with) the coefficient of the term of
-- index /i/ of /A/.
foreign import ccall "nmod_mpoly.h nmod_mpoly_univar_swap_term_coeff"
  nmod_mpoly_univar_swap_term_coeff :: Ptr CNModMPoly -> Ptr CNModMPolyUnivar -> CLong -> Ptr CNModMPolyCtx -> IO ()

-- Internal Functions ----------------------------------------------------------

-- | /nmod_mpoly_pow_rmul/ /A/ /B/ /k/ /ctx/ 
--
-- Set /A/ to /B/ raised to the /k/-th power using repeated
-- multiplications.
foreign import ccall "nmod_mpoly.h nmod_mpoly_pow_rmul"
  nmod_mpoly_pow_rmul :: Ptr CNModMPoly -> Ptr CNModMPoly -> CULong -> Ptr CNModMPolyCtx -> IO ()

-- | /nmod_mpoly_div_monagan_pearce/ /polyq/ /poly2/ /poly3/ /ctx/ 
--
-- Set @polyq@ to the quotient of @poly2@ by @poly3@, discarding the
-- remainder (with notional remainder coefficients reduced modulo the
-- leading coefficient of @poly3@). Implements \"Polynomial division using
-- dynamic arrays, heaps and packed exponents\" by Michael Monagan and
-- Roman Pearce. This function is exceptionally efficient if the division
-- is known to be exact.
foreign import ccall "nmod_mpoly.h nmod_mpoly_div_monagan_pearce"
  nmod_mpoly_div_monagan_pearce :: Ptr CNModMPoly -> Ptr CNModMPoly -> Ptr CNModMPoly -> Ptr CNModMPolyCtx -> IO ()

-- | /nmod_mpoly_divrem_monagan_pearce/ /q/ /r/ /poly2/ /poly3/ /ctx/ 
--
-- Set @polyq@ and @polyr@ to the quotient and remainder of @poly2@ divided
-- by @poly3@, (with remainder coefficients reduced modulo the leading
-- coefficient of @poly3@). Implements \"Polynomial division using dynamic
-- arrays, heaps and packed exponents\" by Michael Monagan and Roman
-- Pearce.
foreign import ccall "nmod_mpoly.h nmod_mpoly_divrem_monagan_pearce"
  nmod_mpoly_divrem_monagan_pearce :: Ptr CNModMPoly -> Ptr CNModMPoly -> Ptr CNModMPoly -> Ptr CNModMPoly -> Ptr CNModMPolyCtx -> IO ()

-- | /nmod_mpoly_divrem_ideal_monagan_pearce/ /q/ /r/ /poly2/ /poly3/ /len/ /ctx/ 
--
-- This function is as per @nmod_mpoly_divrem_monagan_pearce@ except that
-- it takes an array of divisor polynomials @poly3@, and it returns an
-- array of quotient polynomials @q@. The number of divisor (and hence
-- quotient) polynomials, is given by /len/. The function computes
-- polynomials \(q_i = q[i]\) such that @poly2@ is
-- \(r + \sum_{i=0}^{\mbox{len - 1}} q_ib_i\), where \(b_i =\) @poly3[i]@.
foreign import ccall "nmod_mpoly.h nmod_mpoly_divrem_ideal_monagan_pearce"
  nmod_mpoly_divrem_ideal_monagan_pearce :: Ptr (Ptr (Ptr CNModMPoly)) -> Ptr CNModMPoly -> Ptr CNModMPoly -> Ptr (Ptr (Ptr CNModMPoly)) -> CLong -> Ptr CNModMPolyCtx -> IO ()

