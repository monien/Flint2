
module Data.Number.Flint.Fmpq.MPoly.FFI (
  -- * Multivariate polynomials over the rational numbers
    FmpqMPoly (..)
  , CFmpqMPoly (..)
  , newFmpqMPoly
  , withFmpqMPoly
  -- * Context object
  , FmpqMPolyCtx (..)
  , CFmpqMPolyCtx (..)
  , newFmpqMPolyCtx
  , withFmpqMPolyCtx
  -- * 
  , fmpq_mpoly_ctx_init
  , fmpq_mpoly_ctx_nvars
  , fmpq_mpoly_ctx_ord
  , fmpq_mpoly_ctx_clear
  -- * Memory management
  , fmpq_mpoly_init
  , fmpq_mpoly_init2
  , fmpq_mpoly_init3
  , fmpq_mpoly_fit_length
  , fmpq_mpoly_fit_bits
  , fmpq_mpoly_realloc
  , fmpq_mpoly_clear
  -- * Input\/Output
  , fmpq_mpoly_get_str_pretty
  , fmpq_mpoly_fprint_pretty
  , fmpq_mpoly_print_pretty
  , fmpq_mpoly_set_str_pretty
  -- * Basic manipulation
  , fmpq_mpoly_gen
  , fmpq_mpoly_is_gen
  , fmpq_mpoly_set
  , fmpq_mpoly_equal
  , fmpq_mpoly_swap
  -- * Constants
  , fmpq_mpoly_is_fmpq
  , fmpq_mpoly_get_fmpq
  , fmpq_mpoly_set_fmpq
  , fmpq_mpoly_set_fmpz
  , fmpq_mpoly_set_ui
  , fmpq_mpoly_set_si
  , fmpq_mpoly_zero
  , fmpq_mpoly_one
  , fmpq_mpoly_equal_fmpq
  , fmpq_mpoly_equal_fmpz
  , fmpq_mpoly_equal_ui
  , fmpq_mpoly_equal_si
  , fmpq_mpoly_is_zero
  , fmpq_mpoly_is_one
  -- * Degrees
  , fmpq_mpoly_degrees_fit_si
  , fmpq_mpoly_degrees_fmpz
  , fmpq_mpoly_degrees_si
  , fmpq_mpoly_degree_fmpz
  , fmpq_mpoly_degree_si
  , fmpq_mpoly_total_degree_fits_si
  , fmpq_mpoly_total_degree_fmpz
  , fmpq_mpoly_total_degree_si
  , fmpq_mpoly_used_vars
  -- * Coefficients
  , fmpq_mpoly_get_denominator
  , fmpq_mpoly_get_coeff_fmpq_monomial
  , fmpq_mpoly_set_coeff_fmpq_monomial
  , fmpq_mpoly_get_coeff_fmpq_fmpz
  , fmpq_mpoly_get_coeff_fmpq_ui
  , fmpq_mpoly_set_coeff_fmpq_fmpz
  , fmpq_mpoly_set_coeff_fmpq_ui
  , fmpq_mpoly_get_coeff_vars_ui
  -- * Comparison
  , fmpq_mpoly_cmp
  -- * Container operations
  , fmpq_mpoly_content_ref
  , fmpq_mpoly_zpoly_ref
  , fmpq_mpoly_zpoly_term_coeff_ref
  , fmpq_mpoly_is_canonical
  , fmpq_mpoly_length
  , fmpq_mpoly_resize
  , fmpq_mpoly_get_term_coeff_fmpq
  , fmpq_mpoly_set_term_coeff_fmpq
  , fmpq_mpoly_term_exp_fits_si
  , fmpq_mpoly_term_exp_fits_ui
  , fmpq_mpoly_get_term_exp_fmpz
  , fmpq_mpoly_get_term_exp_ui
  , fmpq_mpoly_get_term_exp_si
  , fmpq_mpoly_get_term_var_exp_ui
  , fmpq_mpoly_get_term_var_exp_si
  , fmpq_mpoly_set_term_exp_fmpz
  , fmpq_mpoly_set_term_exp_ui
  , fmpq_mpoly_get_term
  , fmpq_mpoly_get_term_monomial
  , fmpq_mpoly_push_term_fmpq_fmpz
  , fmpq_mpoly_push_term_fmpz_fmpz
  , fmpq_mpoly_push_term_ui_fmpz
  , fmpq_mpoly_push_term_si_fmpz
  , fmpq_mpoly_push_term_fmpq_ui
  , fmpq_mpoly_push_term_fmpz_ui
  , fmpq_mpoly_push_term_ui_ui
  , fmpq_mpoly_push_term_si_ui
  , fmpq_mpoly_reduce
  , fmpq_mpoly_sort_terms
  , fmpq_mpoly_combine_like_terms
  -- , fmpq_mpoly_reverse
  -- * Random generation
  , fmpq_mpoly_randtest_bound
  , fmpq_mpoly_randtest_bounds
  , fmpq_mpoly_randtest_bits
  -- * Addition\/Subtraction
  , fmpq_mpoly_add_fmpq
  , fmpq_mpoly_add_fmpz
  , fmpq_mpoly_add_ui
  , fmpq_mpoly_add_si
  , fmpq_mpoly_sub_fmpq
  , fmpq_mpoly_sub_fmpz
  , fmpq_mpoly_sub_ui
  , fmpq_mpoly_sub_si
  , fmpq_mpoly_add
  , fmpq_mpoly_sub
  -- * Scalar operations
  , fmpq_mpoly_neg
  , fmpq_mpoly_scalar_mul_fmpq
  , fmpq_mpoly_scalar_mul_fmpz
  , fmpq_mpoly_scalar_mul_ui
  , fmpq_mpoly_scalar_mul_si
  , fmpq_mpoly_scalar_div_fmpq
  , fmpq_mpoly_scalar_div_fmpz
  , fmpq_mpoly_scalar_div_ui
  , fmpq_mpoly_scalar_div_si
  , fmpq_mpoly_make_monic
  -- * Differentiation\/Integration
  , fmpq_mpoly_derivative
  , fmpq_mpoly_integral
  -- * Evaluation
  , fmpq_mpoly_evaluate_all_fmpq
  , fmpq_mpoly_evaluate_one_fmpq
  , fmpq_mpoly_compose_fmpq_poly
  , fmpq_mpoly_compose_fmpq_mpoly
  , fmpq_mpoly_compose_fmpq_mpoly_gen
  -- * Multiplication
  , fmpq_mpoly_mul
  -- * Powering
  , fmpq_mpoly_pow_fmpz
  , fmpq_mpoly_pow_ui
  -- * Division
  , fmpq_mpoly_divides
  , fmpq_mpoly_div
  , fmpq_mpoly_divrem
  , fmpq_mpoly_divrem_ideal
  -- * Greatest Common Divisor
  , fmpq_mpoly_content
  , fmpq_mpoly_term_content
  , fmpq_mpoly_content_vars
  , fmpq_mpoly_gcd
  , fmpq_mpoly_gcd_cofactors
  , fmpq_mpoly_gcd_brown
  , fmpq_mpoly_gcd_hensel
  , fmpq_mpoly_gcd_subresultant
  , fmpq_mpoly_gcd_zippel
  , fmpq_mpoly_gcd_zippel2
  , fmpq_mpoly_resultant
  , fmpq_mpoly_discriminant
  -- * Square Root
  , fmpq_mpoly_sqrt
  , fmpq_mpoly_is_square
  -- * Univariate Functions
  , fmpq_mpoly_univar_init
  , fmpq_mpoly_univar_clear
  , fmpq_mpoly_univar_swap
  , fmpq_mpoly_to_univar
  , fmpq_mpoly_from_univar
  , fmpq_mpoly_univar_degree_fits_si
  , fmpq_mpoly_univar_length
  , fmpq_mpoly_univar_get_term_exp_si
  , fmpq_mpoly_univar_get_term_coeff
  , fmpq_mpoly_univar_swap_term_coeff
) where

-- Multivariate polynomials over the rational numbers --------------------------

import Foreign.Ptr
import Foreign.ForeignPtr
import Foreign.C.Types
import Foreign.C.String
import Foreign.Storable
import Foreign.Marshal.Array ( advancePtr )

import Data.Number.Flint.Flint
import Data.Number.Flint.MPoly
import Data.Number.Flint.Fmpz
import Data.Number.Flint.Fmpz.Poly
import Data.Number.Flint.Fmpz.MPoly
import Data.Number.Flint.Fmpz.MPoly.Q
import Data.Number.Flint.Fmpq
import Data.Number.Flint.Fmpq.Poly

#include <flint/fmpq.h>
#include <flint/fmpq_types.h>
#include <flint/fmpq_mpoly.h>
#include <flint/mpoly_types.h>

-- fmpq_mpoly_t ----------------------------------------------------------------

data FmpqMPoly = FmpqMPoly {-# UNPACK #-} !(ForeignPtr CFmpqMPoly)
data CFmpqMPoly = CFmpqMPoly CFmpq CFmpzMPoly

instance Storable CFmpqMPoly where
  sizeOf    _ = #{size      fmpq_mpoly_t}
  alignment _ = #{alignment fmpq_mpoly_t}
  peek ptr = CFmpqMPoly
    <$> #{peek fmpq_mpoly_struct, content} ptr
    <*> #{peek fmpq_mpoly_struct, zpoly  } ptr
  poke ptr (CFmpqMPoly content zpoly) = do
    #{poke fmpq_mpoly_struct, content} ptr content
    #{poke fmpq_mpoly_struct, zpoly  } ptr zpoly
      
newFmpqMPoly ctx@(FmpqMPolyCtx pctx) = do
  x <- mallocForeignPtr
  withForeignPtr x $ \x -> do
    withFmpqMPolyCtx ctx $ \ctx -> do
      fmpq_mpoly_init x ctx
      addForeignPtrFinalizerEnv p_fmpq_mpoly_clear x pctx
  return $ FmpqMPoly x

withFmpqMPoly (FmpqMPoly x) f = do
  withForeignPtr x $ \xp -> (FmpqMPoly x,) <$> f xp

-- fmpq_mpoly_univar_t ---------------------------------------------------------

data FmpqMPolyUniVar = FmpqMPolyUniVar {-# UNPACK #-} !(ForeignPtr CFmpqMPolyUniVar)
data CFmpqMPolyUniVar = CFmpqMPolyUniVar 

instance Storable CFmpqMPolyUniVar where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size fmpq_mpoly_univar_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment fmpq_mpoly_univar_t}
  peek = error "CFmpqMPolyUniVar.peek: Not defined"
  poke = error "CFmpqMPolyUniVar.poke: Not defined"

-- | Create a new `FmpqMPolyUniVar`
newFmpqMPolyUniVar ctx@(FmpqMPolyCtx pctx) = do
  p <- mallocForeignPtr
  withForeignPtr p $ \p ->
    withFmpqMPolyCtx ctx $ \ctx -> do 
      fmpq_mpoly_univar_init p ctx
      addForeignPtrFinalizerEnv p_fmpq_mpoly_univar_clear p pctx
  return $ FmpqMPolyUniVar p

{-# INLINE withFmpqMPolyUniVar #-}
withFmpqMPolyUniVar (FmpqMPolyUniVar p) f = do
  withForeignPtr p $ \fp -> (FmpqMPolyUniVar p,) <$> f fp
  
-- fmpz_mpoly_ctx_t ------------------------------------------------------------

data FmpqMPolyCtx = FmpqMPolyCtx {-# UNPACK #-} !(ForeignPtr CFmpqMPolyCtx)
data CFmpqMPolyCtx

instance Storable CFmpqMPolyCtx where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size fmpq_mpoly_ctx_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment fmpq_mpoly_ctx_t}
  peek = error "CFmpqMPolyCtx.peek: Not defined"
  poke = error "CFmpqMPolyCtx.poke: Not defined"

-- | Create a new `FmpqMPolyCtx`
newFmpqMPolyCtx nvars ord = do
  p <- mallocForeignPtr
  withForeignPtr p $ \p ->
    fmpq_mpoly_ctx_init p nvars ord
  addForeignPtrFinalizer p_fmpq_mpoly_ctx_clear p
  return $ FmpqMPolyCtx p

-- | Use a `FmpqMPolyCtx`
{-# INLINE withFmpqMPolyCtx #-}
withFmpqMPolyCtx (FmpqMPolyCtx p) f = do
  withForeignPtr p $ \fp -> f fp >>= return . (FmpqMPolyCtx p,)

-- Context object --------------------------------------------------------------

-- | /fmpq_mpoly_ctx_init/ /ctx/ /nvars/ /ord/ 
--
-- Initialise a context object for a polynomial ring with the given number
-- of variables and the given ordering. The possibilities for the ordering
-- are @ORD_LEX@, @ORD_DEGLEX@ and @ORD_DEGREVLEX@.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_ctx_init"
  fmpq_mpoly_ctx_init :: Ptr CFmpqMPolyCtx -> CLong -> Ptr COrdering -> IO ()

-- | /fmpq_mpoly_ctx_nvars/ /ctx/ 
--
-- Return the number of variables used to initialize the context.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_ctx_nvars"
  fmpq_mpoly_ctx_nvars :: Ptr CFmpqMPolyCtx -> IO CLong

-- | /fmpq_mpoly_ctx_ord/ /ctx/ 
--
-- Return the ordering used to initialize the context.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_ctx_ord"
  fmpq_mpoly_ctx_ord :: Ptr CFmpqMPolyCtx -> IO (Ptr COrdering)

-- | /fmpq_mpoly_ctx_clear/ /ctx/ 
--
-- Release up any space allocated by /ctx/.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_ctx_clear"
  fmpq_mpoly_ctx_clear :: Ptr CFmpqMPolyCtx -> IO ()

foreign import ccall "fmpq_mpoly.h &fmpq_mpoly_ctx_clear"
  p_fmpq_mpoly_ctx_clear :: FunPtr (Ptr CFmpqMPolyCtx -> IO ())

-- Memory management -----------------------------------------------------------

-- | /fmpq_mpoly_init/ /A/ /ctx/ 
--
-- Initialise /A/ for use with the given and initialised context object.
-- Its value is set to zero.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_init"
  fmpq_mpoly_init :: Ptr CFmpqMPoly -> Ptr CFmpqMPolyCtx -> IO ()

-- | /fmpq_mpoly_init2/ /A/ /alloc/ /ctx/ 
--
-- Initialise /A/ for use with the given and initialised context object.
-- Its value is set to zero. It is allocated with space for /alloc/ terms
-- and at least @MPOLY_MIN_BITS@ bits for the exponents.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_init2"
  fmpq_mpoly_init2 :: Ptr CFmpqMPoly -> CLong -> Ptr CFmpqMPolyCtx -> IO ()

-- | /fmpq_mpoly_init3/ /A/ /alloc/ /bits/ /ctx/ 
--
-- Initialise /A/ for use with the given and initialised context object.
-- Its value is set to zero. It is allocated with space for /alloc/ terms
-- and /bits/ bits for the exponents.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_init3"
  fmpq_mpoly_init3 :: Ptr CFmpqMPoly -> CLong -> CFBitCnt -> Ptr CFmpqMPolyCtx -> IO ()

-- | /fmpq_mpoly_fit_length/ /A/ /len/ /ctx/ 
--
-- Ensure that /A/ has space for at least /len/ terms.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_fit_length"
  fmpq_mpoly_fit_length :: Ptr CFmpqMPoly -> CLong -> Ptr CFmpqMPolyCtx -> IO ()

-- | /fmpq_mpoly_fit_bits/ /A/ /bits/ /ctx/ 
--
-- Ensure that the exponent fields of /A/ have at least /bits/ bits.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_fit_bits"
  fmpq_mpoly_fit_bits :: Ptr CFmpqMPoly -> CFBitCnt -> Ptr CFmpqMPolyCtx -> IO ()

-- | /fmpq_mpoly_realloc/ /A/ /alloc/ /ctx/ 
--
-- Reallocate /A/ to have space for /alloc/ terms. Assumes the current
-- length of the polynomial is not greater than /alloc/.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_realloc"
  fmpq_mpoly_realloc :: Ptr CFmpqMPoly -> CLong -> Ptr CFmpqMPolyCtx -> IO ()

-- | /fmpq_mpoly_clear/ /A/ /ctx/ 
--
-- Release any space allocated for /A/.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_clear"
  fmpq_mpoly_clear :: Ptr CFmpqMPoly -> Ptr CFmpqMPolyCtx -> IO ()

foreign import ccall "fmpq_mpoly.h &fmpq_mpoly_clear"
  p_fmpq_mpoly_clear :: FunPtr (Ptr CFmpqMPoly -> Ptr CFmpqMPolyCtx -> IO ())

-- Input\/Output ---------------------------------------------------------------

-- | /fmpq_mpoly_get_str_pretty/ /A/ /x/ /ctx/ 
--
-- Return a string, which the user is responsible for cleaning up,
-- representing /A/, given an array of variable strings @x@.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_get_str_pretty"
  fmpq_mpoly_get_str_pretty :: Ptr CFmpqMPoly -> Ptr (Ptr CChar) -> Ptr CFmpqMPolyCtx -> IO CString

-- | /fmpq_mpoly_fprint_pretty/ /file/ /A/ /x/ /ctx/ 
--
-- Print a string representing /A/ to /file/.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_fprint_pretty"
  fmpq_mpoly_fprint_pretty :: Ptr CFile -> Ptr CFmpqMPoly -> Ptr (Ptr CChar) -> Ptr CFmpqMPolyCtx -> IO CInt

-- | /fmpq_mpoly_print_pretty/ /A/ /x/ /ctx/ 
--
-- Print a string representing /A/ to @stdout@.
-- foreign import ccall "fmpq_mpoly.h fmpq_mpoly_print_pretty"
fmpq_mpoly_print_pretty :: Ptr CFmpqMPoly
                        -> Ptr (Ptr CChar)
                        -> Ptr CFmpqMPolyCtx
                        -> IO CInt
fmpq_mpoly_print_pretty a x ctx = 
  printCStr (\a -> fmpq_mpoly_get_str_pretty a x ctx) a

-- | /fmpq_mpoly_set_str_pretty/ /A/ /str/ /x/ /ctx/ 
--
-- Set /A/ to the polynomial in the null-terminates string @str@ given an
-- array @x@ of variable strings. If parsing @str@ fails, /A/ is set to
-- zero, and \(-1\) is returned. Otherwise, \(0\) is returned. The
-- operations @+@, @-@, @*@, and @\/@ are permitted along with integers and
-- the variables in @x@. The character @^@ must be immediately followed by
-- the (integer) exponent. If any division is not exact, parsing fails.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_set_str_pretty"
  fmpq_mpoly_set_str_pretty :: Ptr CFmpqMPoly -> CString -> Ptr (Ptr CChar) -> Ptr CFmpqMPolyCtx -> IO CInt

-- Basic manipulation ----------------------------------------------------------

-- | /fmpq_mpoly_gen/ /A/ /var/ /ctx/ 
--
-- Set /A/ to the variable of index /var/, where @var = 0@ corresponds to
-- the variable with the most significance with respect to the ordering.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_gen"
  fmpq_mpoly_gen :: Ptr CFmpqMPoly -> CLong -> Ptr CFmpqMPolyCtx -> IO ()

-- | /fmpq_mpoly_is_gen/ /A/ /var/ /ctx/ 
--
-- If \(var \ge 0\), return \(1\) if /A/ is equal to the \(var\)-th
-- generator, otherwise return \(0\). If \(var < 0\), return \(1\) if the
-- polynomial is equal to any generator, otherwise return \(0\).
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_is_gen"
  fmpq_mpoly_is_gen :: Ptr CFmpqMPoly -> CLong -> Ptr CFmpqMPolyCtx -> IO CInt

-- | /fmpq_mpoly_set/ /A/ /B/ /ctx/ 
--
-- Set /A/ to /B/.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_set"
  fmpq_mpoly_set :: Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> Ptr CFmpqMPolyCtx -> IO ()

-- | /fmpq_mpoly_equal/ /A/ /B/ /ctx/ 
--
-- Return \(1\) if /A/ is equal to /B/, else return \(0\).
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_equal"
  fmpq_mpoly_equal :: Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> Ptr CFmpqMPolyCtx -> IO CInt

-- | /fmpq_mpoly_swap/ /A/ /B/ /ctx/ 
--
-- Efficiently swap /A/ and /B/.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_swap"
  fmpq_mpoly_swap :: Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> Ptr CFmpqMPolyCtx -> IO ()

-- Constants -------------------------------------------------------------------

-- | /fmpq_mpoly_is_fmpq/ /A/ /ctx/ 
--
-- Return \(1\) if /A/ is a constant, else return \(0\).
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_is_fmpq"
  fmpq_mpoly_is_fmpq :: Ptr CFmpqMPoly -> Ptr CFmpqMPolyCtx -> IO CInt

-- | /fmpq_mpoly_get_fmpq/ /c/ /A/ /ctx/ 
--
-- Assuming that /A/ is a constant, set /c/ to this constant. This function
-- throws if /A/ is not a constant.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_get_fmpq"
  fmpq_mpoly_get_fmpq :: Ptr CFmpq -> Ptr CFmpqMPoly -> Ptr CFmpqMPolyCtx -> IO ()

-- | /fmpq_mpoly_set_fmpq/ /A/ /c/ /ctx/ 
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_set_fmpq"
  fmpq_mpoly_set_fmpq :: Ptr CFmpqMPoly -> Ptr CFmpq -> Ptr CFmpqMPolyCtx -> IO ()
-- | /fmpq_mpoly_set_fmpz/ /A/ /c/ /ctx/ 
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_set_fmpz"
  fmpq_mpoly_set_fmpz :: Ptr CFmpqMPoly -> Ptr CFmpz -> Ptr CFmpqMPolyCtx -> IO ()
-- | /fmpq_mpoly_set_ui/ /A/ /c/ /ctx/ 
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_set_ui"
  fmpq_mpoly_set_ui :: Ptr CFmpqMPoly -> CULong -> Ptr CFmpqMPolyCtx -> IO ()
-- | /fmpq_mpoly_set_si/ /A/ /c/ /ctx/ 
--
-- Set /A/ to the constant /c/.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_set_si"
  fmpq_mpoly_set_si :: Ptr CFmpqMPoly -> CLong -> Ptr CFmpqMPolyCtx -> IO ()

-- | /fmpq_mpoly_zero/ /A/ /ctx/ 
--
-- Set /A/ to the constant \(0\).
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_zero"
  fmpq_mpoly_zero :: Ptr CFmpqMPoly -> Ptr CFmpqMPolyCtx -> IO ()

-- | /fmpq_mpoly_one/ /A/ /ctx/ 
--
-- Set /A/ to the constant \(1\).
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_one"
  fmpq_mpoly_one :: Ptr CFmpqMPoly -> Ptr CFmpqMPolyCtx -> IO ()

-- | /fmpq_mpoly_equal_fmpq/ /A/ /c/ /ctx/ 
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_equal_fmpq"
  fmpq_mpoly_equal_fmpq :: Ptr CFmpqMPoly -> Ptr CFmpq -> Ptr CFmpqMPolyCtx -> IO CInt
-- | /fmpq_mpoly_equal_fmpz/ /A/ /c/ /ctx/ 
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_equal_fmpz"
  fmpq_mpoly_equal_fmpz :: Ptr CFmpqMPoly -> Ptr CFmpz -> Ptr CFmpqMPolyCtx -> IO CInt
-- | /fmpq_mpoly_equal_ui/ /A/ /c/ /ctx/ 
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_equal_ui"
  fmpq_mpoly_equal_ui :: Ptr CFmpqMPoly -> CULong -> Ptr CFmpqMPolyCtx -> IO CInt
-- | /fmpq_mpoly_equal_si/ /A/ /c/ /ctx/ 
--
-- Return \(1\) if /A/ is equal to the constant /c/, else return \(0\).
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_equal_si"
  fmpq_mpoly_equal_si :: Ptr CFmpqMPoly -> CLong -> Ptr CFmpqMPolyCtx -> IO CInt

-- | /fmpq_mpoly_is_zero/ /A/ /ctx/ 
--
-- Return \(1\) if /A/ is equal to the constant \(0\), else return \(0\).
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_is_zero"
  fmpq_mpoly_is_zero :: Ptr CFmpqMPoly -> Ptr CFmpqMPolyCtx -> IO CInt

-- | /fmpq_mpoly_is_one/ /A/ /ctx/ 
--
-- Return \(1\) if /A/ is equal to the constant \(1\), else return \(0\).
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_is_one"
  fmpq_mpoly_is_one :: Ptr CFmpqMPoly -> Ptr CFmpqMPolyCtx -> IO CInt

-- Degrees ---------------------------------------------------------------------

-- | /fmpq_mpoly_degrees_fit_si/ /A/ /ctx/ 
--
-- Return \(1\) if the degrees of /A/ with respect to each variable fit
-- into an @slong@, otherwise return \(0\).
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_degrees_fit_si"
  fmpq_mpoly_degrees_fit_si :: Ptr CFmpqMPoly -> Ptr CFmpqMPolyCtx -> IO CInt

-- | /fmpq_mpoly_degrees_fmpz/ /degs/ /A/ /ctx/ 
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_degrees_fmpz"
  fmpq_mpoly_degrees_fmpz :: Ptr (Ptr CFmpz) -> Ptr CFmpqMPoly -> Ptr CFmpqMPolyCtx -> IO ()
-- | /fmpq_mpoly_degrees_si/ /degs/ /A/ /ctx/ 
--
-- Set /degs/ to the degrees of /A/ with respect to each variable. If /A/
-- is zero, all degrees are set to \(-1\).
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_degrees_si"
  fmpq_mpoly_degrees_si :: Ptr CLong -> Ptr CFmpqMPoly -> Ptr CFmpqMPolyCtx -> IO ()

-- | /fmpq_mpoly_degree_fmpz/ /deg/ /A/ /var/ /ctx/ 
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_degree_fmpz"
  fmpq_mpoly_degree_fmpz :: Ptr CFmpz -> Ptr CFmpqMPoly -> CLong -> Ptr CFmpqMPolyCtx -> IO ()
-- | /fmpq_mpoly_degree_si/ /A/ /var/ /ctx/ 
--
-- Either return or set /deg/ to the degree of /A/ with respect to the
-- variable of index /var/. If /A/ is zero, the degree is defined to be
-- \(-1\).
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_degree_si"
  fmpq_mpoly_degree_si :: Ptr CFmpqMPoly -> CLong -> Ptr CFmpqMPolyCtx -> IO CLong

-- | /fmpq_mpoly_total_degree_fits_si/ /A/ /ctx/ 
--
-- Return \(1\) if the total degree of /A/ fits into an @slong@, otherwise
-- return \(0\).
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_total_degree_fits_si"
  fmpq_mpoly_total_degree_fits_si :: Ptr CFmpqMPoly -> Ptr CFmpqMPolyCtx -> IO CInt

-- | /fmpq_mpoly_total_degree_fmpz/ /tdeg/ /A/ /ctx/ 
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_total_degree_fmpz"
  fmpq_mpoly_total_degree_fmpz :: Ptr CFmpz -> Ptr CFmpqMPoly -> Ptr CFmpqMPolyCtx -> IO ()
-- | /fmpq_mpoly_total_degree_si/ /A/ /ctx/ 
--
-- Either return or set /tdeg/ to the total degree of /A/. If /A/ is zero,
-- the total degree is defined to be \(-1\).
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_total_degree_si"
  fmpq_mpoly_total_degree_si :: Ptr CFmpqMPoly -> Ptr CFmpqMPolyCtx -> IO CLong

-- | /fmpq_mpoly_used_vars/ /used/ /A/ /ctx/ 
--
-- For each variable index /i/, set @used[i]@ to nonzero if the variable of
-- index /i/ appears in /A/ and to zero otherwise.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_used_vars"
  fmpq_mpoly_used_vars :: Ptr CInt -> Ptr CFmpqMPoly -> Ptr CFmpqMPolyCtx -> IO ()

-- Coefficients ----------------------------------------------------------------

-- | /fmpq_mpoly_get_denominator/ /d/ /A/ /ctx/ 
--
-- Set /d/ to the denominator of /A/, the smallest positive integer \(d\)
-- such that \(d \times A\) has integer coefficients.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_get_denominator"
  fmpq_mpoly_get_denominator :: Ptr CFmpz -> Ptr CFmpqMPoly -> Ptr CFmpqMPolyCtx -> IO ()

-- | /fmpq_mpoly_get_coeff_fmpq_monomial/ /c/ /A/ /M/ /ctx/ 
--
-- Assuming that /M/ is a monomial, set /c/ to the coefficient of the
-- corresponding monomial in /A/. This function throws if /M/ is not a
-- monomial.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_get_coeff_fmpq_monomial"
  fmpq_mpoly_get_coeff_fmpq_monomial :: Ptr CFmpq -> Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> Ptr CFmpqMPolyCtx -> IO ()

-- | /fmpq_mpoly_set_coeff_fmpq_monomial/ /A/ /c/ /M/ /ctx/ 
--
-- Assuming that /M/ is a monomial, set the coefficient of the
-- corresponding monomial in /A/ to /c/. This function throws if /M/ is not
-- a monomial.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_set_coeff_fmpq_monomial"
  fmpq_mpoly_set_coeff_fmpq_monomial :: Ptr CFmpqMPoly -> Ptr CFmpq -> Ptr CFmpqMPoly -> Ptr CFmpqMPolyCtx -> IO ()

-- | /fmpq_mpoly_get_coeff_fmpq_fmpz/ /c/ /A/ /exp/ /ctx/ 
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_get_coeff_fmpq_fmpz"
  fmpq_mpoly_get_coeff_fmpq_fmpz :: Ptr CFmpq -> Ptr CFmpqMPoly -> Ptr (Ptr CFmpz) -> Ptr CFmpqMPolyCtx -> IO ()
-- | /fmpq_mpoly_get_coeff_fmpq_ui/ /c/ /A/ /exp/ /ctx/ 
--
-- Set /c/ to the coefficient of the monomial with exponent /exp/.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_get_coeff_fmpq_ui"
  fmpq_mpoly_get_coeff_fmpq_ui :: Ptr CFmpq -> Ptr CFmpqMPoly -> Ptr CULong -> Ptr CFmpqMPolyCtx -> IO ()

-- | /fmpq_mpoly_set_coeff_fmpq_fmpz/ /A/ /c/ /exp/ /ctx/ 
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_set_coeff_fmpq_fmpz"
  fmpq_mpoly_set_coeff_fmpq_fmpz :: Ptr CFmpqMPoly -> Ptr CFmpq -> Ptr (Ptr CFmpz) -> Ptr CFmpqMPolyCtx -> IO ()
-- | /fmpq_mpoly_set_coeff_fmpq_ui/ /A/ /c/ /exp/ /ctx/ 
--
-- Set the coefficient of the monomial with exponent /exp/ to /c/.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_set_coeff_fmpq_ui"
  fmpq_mpoly_set_coeff_fmpq_ui :: Ptr CFmpqMPoly -> Ptr CFmpq -> Ptr CULong -> Ptr CFmpqMPolyCtx -> IO ()

-- | /fmpq_mpoly_get_coeff_vars_ui/ /C/ /A/ /vars/ /exps/ /length/ /ctx/ 
--
-- Set /C/ to the coefficient of /A/ with respect to the variables in
-- /vars/ with powers in the corresponding array /exps/. Both /vars/ and
-- /exps/ point to array of length /length/. It is assumed that
-- \(0 < length \le nvars(A)\) and that the variables in /vars/ are
-- distinct.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_get_coeff_vars_ui"
  fmpq_mpoly_get_coeff_vars_ui :: Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> Ptr CLong -> Ptr CULong -> CLong -> Ptr CFmpqMPolyCtx -> IO ()

-- Comparison ------------------------------------------------------------------

-- | /fmpq_mpoly_cmp/ /A/ /B/ /ctx/ 
--
-- Return \(1\) (resp. \(-1\), or \(0\)) if /A/ is after (resp. before,
-- same as) /B/ in some arbitrary but fixed total ordering of the
-- polynomials. This ordering agrees with the usual ordering of monomials
-- when /A/ and /B/ are both monomials.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_cmp"
  fmpq_mpoly_cmp :: Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> Ptr CFmpqMPolyCtx -> IO CInt

-- Container operations --------------------------------------------------------




-- | /fmpq_mpoly_content_ref/ /A/ /ctx/ 
--
-- Return a reference to the content of /A/.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_content_ref"
  fmpq_mpoly_content_ref :: Ptr CFmpqMPoly -> Ptr CFmpqMPolyCtx -> IO (Ptr CFmpq)

-- | /fmpq_mpoly_zpoly_ref/ /A/ /ctx/ 
--
-- Return a reference to the integer polynomial of /A/.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_zpoly_ref"
  fmpq_mpoly_zpoly_ref :: Ptr CFmpqMPoly -> Ptr CFmpqMPolyCtx -> IO (Ptr (Ptr CFmpzMPoly))

-- | /fmpq_mpoly_zpoly_term_coeff_ref/ /A/ /i/ /ctx/ 
--
-- Return a reference to the coefficient of index /i/ of the integer
-- polynomial of /A/.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_zpoly_term_coeff_ref"
  fmpq_mpoly_zpoly_term_coeff_ref :: Ptr CFmpqMPoly -> CLong -> Ptr CFmpqMPolyCtx -> IO (Ptr CFmpz)

-- | /fmpq_mpoly_is_canonical/ /A/ /ctx/ 
--
-- Return \(1\) if /A/ is in canonical form. Otherwise, return \(0\). An
-- @fmpq_mpoly_t@ is represented as the product of an @fmpq_t content@ and
-- an @fmpz_mpoly_t zpoly@. The representation is considered canonical when
-- either (1) both @content@ and @zpoly@ are zero, or (2) both @content@
-- and @zpoly@ are nonzero and canonical and @zpoly@ is reduced. A nonzero
-- @zpoly@ is considered reduced when the coefficients have GCD one and the
-- leading coefficient is positive.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_is_canonical"
  fmpq_mpoly_is_canonical :: Ptr CFmpqMPoly -> Ptr CFmpqMPolyCtx -> IO CInt

-- | /fmpq_mpoly_length/ /A/ /ctx/ 
--
-- Return the number of terms stored in /A/. If the polynomial is in
-- canonical form, this will be the number of nonzero coefficients.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_length"
  fmpq_mpoly_length :: Ptr CFmpqMPoly -> Ptr CFmpqMPolyCtx -> IO CLong

-- | /fmpq_mpoly_resize/ /A/ /new_length/ /ctx/ 
--
-- Set the length of /A/ to @new_length@. Terms are either deleted from the
-- end, or new zero terms are appended.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_resize"
  fmpq_mpoly_resize :: Ptr CFmpqMPoly -> CLong -> Ptr CFmpqMPolyCtx -> IO ()

-- | /fmpq_mpoly_get_term_coeff_fmpq/ /c/ /A/ /i/ /ctx/ 
--
-- Set /c/ to coefficient of index /i/
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_get_term_coeff_fmpq"
  fmpq_mpoly_get_term_coeff_fmpq :: Ptr CFmpq -> Ptr CFmpqMPoly -> CLong -> Ptr CFmpqMPolyCtx -> IO ()

-- | /fmpq_mpoly_set_term_coeff_fmpq/ /A/ /i/ /c/ /ctx/ 
--
-- Set the coefficient of index /i/ to /c/.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_set_term_coeff_fmpq"
  fmpq_mpoly_set_term_coeff_fmpq :: Ptr CFmpqMPoly -> CLong -> Ptr CFmpq -> Ptr CFmpqMPolyCtx -> IO ()

-- | /fmpq_mpoly_term_exp_fits_si/ /A/ /i/ /ctx/ 
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_term_exp_fits_si"
  fmpq_mpoly_term_exp_fits_si :: Ptr CFmpqMPoly -> CLong -> Ptr CFmpqMPolyCtx -> IO CInt
-- | /fmpq_mpoly_term_exp_fits_ui/ /A/ /i/ /ctx/ 
--
-- Return \(1\) if all entries of the exponent vector of the term of index
-- /i/ fit into an @slong@ (resp. a @ulong@). Otherwise, return \(0\).
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_term_exp_fits_ui"
  fmpq_mpoly_term_exp_fits_ui :: Ptr CFmpqMPoly -> CLong -> Ptr CFmpqMPolyCtx -> IO CInt

-- | /fmpq_mpoly_get_term_exp_fmpz/ /exps/ /A/ /i/ /ctx/ 
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_get_term_exp_fmpz"
  fmpq_mpoly_get_term_exp_fmpz :: Ptr (Ptr CFmpz) -> Ptr CFmpqMPoly -> CLong -> Ptr CFmpqMPolyCtx -> IO ()
-- | /fmpq_mpoly_get_term_exp_ui/ /exps/ /A/ /i/ /ctx/ 
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_get_term_exp_ui"
  fmpq_mpoly_get_term_exp_ui :: Ptr CULong -> Ptr CFmpqMPoly -> CLong -> Ptr CFmpqMPolyCtx -> IO ()
-- | /fmpq_mpoly_get_term_exp_si/ /exps/ /A/ /i/ /ctx/ 
--
-- Set /exp/ to the exponent vector of the term of index /i/. The @_ui@
-- (resp. @_si@) version throws if any entry does not fit into a @ulong@
-- (resp. @slong@).
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_get_term_exp_si"
  fmpq_mpoly_get_term_exp_si :: Ptr CLong -> Ptr CFmpqMPoly -> CLong -> Ptr CFmpqMPolyCtx -> IO ()

-- | /fmpq_mpoly_get_term_var_exp_ui/ /A/ /i/ /var/ /ctx/ 
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_get_term_var_exp_ui"
  fmpq_mpoly_get_term_var_exp_ui :: Ptr CFmpqMPoly -> CLong -> CLong -> Ptr CFmpqMPolyCtx -> IO CULong
-- | /fmpq_mpoly_get_term_var_exp_si/ /A/ /i/ /var/ /ctx/ 
--
-- Return the exponent of the variable /var/ of the term of index /i/. This
-- function throws if the exponent does not fit into a @ulong@ (resp.
-- @slong@).
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_get_term_var_exp_si"
  fmpq_mpoly_get_term_var_exp_si :: Ptr CFmpqMPoly -> CLong -> CLong -> Ptr CFmpqMPolyCtx -> IO CLong

-- | /fmpq_mpoly_set_term_exp_fmpz/ /A/ /i/ /exps/ /ctx/ 
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_set_term_exp_fmpz"
  fmpq_mpoly_set_term_exp_fmpz :: Ptr CFmpqMPoly -> CLong -> Ptr (Ptr CFmpz) -> Ptr CFmpqMPolyCtx -> IO ()
-- | /fmpq_mpoly_set_term_exp_ui/ /A/ /i/ /exps/ /ctx/ 
--
-- Set the exponent vector of the term of index /i/ to /exp/.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_set_term_exp_ui"
  fmpq_mpoly_set_term_exp_ui :: Ptr CFmpqMPoly -> CLong -> Ptr CULong -> Ptr CFmpqMPolyCtx -> IO ()

-- | /fmpq_mpoly_get_term/ /M/ /A/ /i/ /ctx/ 
--
-- Set /M/ to the term of index /i/ in /A/.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_get_term"
  fmpq_mpoly_get_term :: Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> CLong -> Ptr CFmpqMPolyCtx -> IO ()

-- | /fmpq_mpoly_get_term_monomial/ /M/ /A/ /i/ /ctx/ 
--
-- Set /M/ to the monomial of the term of index /i/ in /A/. The coefficient
-- of /M/ will be one.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_get_term_monomial"
  fmpq_mpoly_get_term_monomial :: Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> CLong -> Ptr CFmpqMPolyCtx -> IO ()

-- | /fmpq_mpoly_push_term_fmpq_fmpz/ /A/ /c/ /exp/ /ctx/ 
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_push_term_fmpq_fmpz"
  fmpq_mpoly_push_term_fmpq_fmpz :: Ptr CFmpqMPoly -> Ptr CFmpq -> Ptr (Ptr CFmpz) -> Ptr CFmpqMPolyCtx -> IO ()
-- | /fmpq_mpoly_push_term_fmpz_fmpz/ /A/ /c/ /exp/ /ctx/ 
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_push_term_fmpz_fmpz"
  fmpq_mpoly_push_term_fmpz_fmpz :: Ptr CFmpqMPoly -> Ptr CFmpz -> Ptr (Ptr CFmpz) -> Ptr CFmpqMPolyCtx -> IO ()
-- | /fmpq_mpoly_push_term_ui_fmpz/ /A/ /c/ /exp/ /ctx/ 
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_push_term_ui_fmpz"
  fmpq_mpoly_push_term_ui_fmpz :: Ptr CFmpqMPoly -> CULong -> Ptr (Ptr CFmpz) -> Ptr CFmpqMPolyCtx -> IO ()
-- | /fmpq_mpoly_push_term_si_fmpz/ /A/ /c/ /exp/ /ctx/ 
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_push_term_si_fmpz"
  fmpq_mpoly_push_term_si_fmpz :: Ptr CFmpqMPoly -> CLong -> Ptr (Ptr CFmpz) -> Ptr CFmpqMPolyCtx -> IO ()
-- | /fmpq_mpoly_push_term_fmpq_ui/ /A/ /c/ /exp/ /ctx/ 
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_push_term_fmpq_ui"
  fmpq_mpoly_push_term_fmpq_ui :: Ptr CFmpqMPoly -> Ptr CFmpq -> Ptr CULong -> Ptr CFmpqMPolyCtx -> IO ()
-- | /fmpq_mpoly_push_term_fmpz_ui/ /A/ /c/ /exp/ /ctx/ 
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_push_term_fmpz_ui"
  fmpq_mpoly_push_term_fmpz_ui :: Ptr CFmpqMPoly -> Ptr CFmpz -> Ptr CULong -> Ptr CFmpqMPolyCtx -> IO ()
-- | /fmpq_mpoly_push_term_ui_ui/ /A/ /c/ /exp/ /ctx/ 
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_push_term_ui_ui"
  fmpq_mpoly_push_term_ui_ui :: Ptr CFmpqMPoly -> CULong -> Ptr CULong -> Ptr CFmpqMPolyCtx -> IO ()
-- | /fmpq_mpoly_push_term_si_ui/ /A/ /c/ /exp/ /ctx/ 
--
-- Append a term to /A/ with coefficient /c/ and exponent vector /exp/.
-- This function should run in constant average time if the terms pushed
-- have bounded denominator.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_push_term_si_ui"
  fmpq_mpoly_push_term_si_ui :: Ptr CFmpqMPoly -> CLong -> Ptr CULong -> Ptr CFmpqMPolyCtx -> IO ()

-- | /fmpq_mpoly_reduce/ /A/ /ctx/ 
--
-- Factor out necessary content from @A->zpoly@ so that it is reduced. If
-- the terms of /A/ were nonzero and sorted with distinct exponents to
-- begin with, the result will be in canonical form.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_reduce"
  fmpq_mpoly_reduce :: Ptr CFmpqMPoly -> Ptr CFmpqMPolyCtx -> IO ()

-- | /fmpq_mpoly_sort_terms/ /A/ /ctx/ 
--
-- Sort the internal @A->zpoly@ into the canonical ordering dictated by the
-- ordering in /ctx/. This function does not combine like terms, nor does
-- it delete terms with coefficient zero, nor does it reduce.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_sort_terms"
  fmpq_mpoly_sort_terms :: Ptr CFmpqMPoly -> Ptr CFmpqMPolyCtx -> IO ()

-- | /fmpq_mpoly_combine_like_terms/ /A/ /ctx/ 
--
-- Combine adjacent like terms in the internal @A->zpoly@ and then factor
-- out content via a call to @fmpq_mpoly_reduce@. If the terms of /A/ were
-- sorted to begin with, the result will be in canonical form.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_combine_like_terms"
  fmpq_mpoly_combine_like_terms :: Ptr CFmpqMPoly -> Ptr CFmpqMPolyCtx -> IO ()

-- -- | /fmpq_mpoly_reverse/ /A/ /B/ /ctx/ 
-- --
-- -- Set /A/ to the reversal of /B/.
-- foreign import ccall "fmpq_mpoly.h fmpq_mpoly_reverse"
--   fmpq_mpoly_reverse :: Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> Ptr CFmpqMPolyCtx -> IO ()

-- Random generation -----------------------------------------------------------

-- | /fmpq_mpoly_randtest_bound/ /A/ /state/ /length/ /coeff_bits/ /exp_bound/ /ctx/ 
--
-- Generate a random polynomial with length up to /length/ and exponents in
-- the range @[0, exp_bound - 1]@. The exponents of each variable are
-- generated by calls to @n_randint(state, exp_bound)@.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_randtest_bound"
  fmpq_mpoly_randtest_bound :: Ptr CFmpqMPoly -> Ptr CFRandState -> CLong -> CMpLimb -> CULong -> Ptr CFmpqMPolyCtx -> IO ()

-- | /fmpq_mpoly_randtest_bounds/ /A/ /state/ /length/ /coeff_bits/ /exp_bounds/ /ctx/ 
--
-- Generate a random polynomial with length up to /length/ and exponents in
-- the range @[0, exp_bounds[i] - 1]@. The exponents of the variable of
-- index /i/ are generated by calls to @n_randint(state, exp_bounds[i])@.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_randtest_bounds"
  fmpq_mpoly_randtest_bounds :: Ptr CFmpqMPoly -> Ptr CFRandState -> CLong -> CMpLimb -> Ptr CULong -> Ptr CFmpqMPolyCtx -> IO ()

-- | /fmpq_mpoly_randtest_bits/ /A/ /state/ /length/ /coeff_bits/ /exp_bits/ /ctx/ 
--
-- Generate a random polynomial with length up to /length/ and exponents
-- whose packed form does not exceed the given bit count.
-- 
-- The parameter @coeff_bits@ to the three functions
-- @fmpq_mpoly_randtest_{bound|bounds|bits}@ is merely a suggestion for the
-- approximate bit count of the resulting coefficients.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_randtest_bits"
  fmpq_mpoly_randtest_bits :: Ptr CFmpqMPoly -> Ptr CFRandState -> CLong -> CMpLimb -> CMpLimb -> Ptr CFmpqMPolyCtx -> IO ()

-- Addition\/Subtraction -------------------------------------------------------

-- | /fmpq_mpoly_add_fmpq/ /A/ /B/ /c/ /ctx/ 
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_add_fmpq"
  fmpq_mpoly_add_fmpq :: Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> Ptr CFmpq -> Ptr CFmpqMPolyCtx -> IO ()
-- | /fmpq_mpoly_add_fmpz/ /A/ /B/ /c/ /ctx/ 
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_add_fmpz"
  fmpq_mpoly_add_fmpz :: Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> Ptr CFmpz -> Ptr CFmpqMPolyCtx -> IO ()
-- | /fmpq_mpoly_add_ui/ /A/ /B/ /c/ /ctx/ 
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_add_ui"
  fmpq_mpoly_add_ui :: Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> CULong -> Ptr CFmpqMPolyCtx -> IO ()
-- | /fmpq_mpoly_add_si/ /A/ /B/ /c/ /ctx/ 
--
-- Set /A/ to \(B + c\).
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_add_si"
  fmpq_mpoly_add_si :: Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> CLong -> Ptr CFmpqMPolyCtx -> IO ()

-- | /fmpq_mpoly_sub_fmpq/ /A/ /B/ /c/ /ctx/ 
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_sub_fmpq"
  fmpq_mpoly_sub_fmpq :: Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> Ptr CFmpq -> Ptr CFmpqMPolyCtx -> IO ()
-- | /fmpq_mpoly_sub_fmpz/ /A/ /B/ /c/ /ctx/ 
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_sub_fmpz"
  fmpq_mpoly_sub_fmpz :: Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> Ptr CFmpz -> Ptr CFmpqMPolyCtx -> IO ()
-- | /fmpq_mpoly_sub_ui/ /A/ /B/ /c/ /ctx/ 
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_sub_ui"
  fmpq_mpoly_sub_ui :: Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> CULong -> Ptr CFmpqMPolyCtx -> IO ()
-- | /fmpq_mpoly_sub_si/ /A/ /B/ /c/ /ctx/ 
--
-- Set /A/ to \(B - c\).
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_sub_si"
  fmpq_mpoly_sub_si :: Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> CLong -> Ptr CFmpqMPolyCtx -> IO ()

-- | /fmpq_mpoly_add/ /A/ /B/ /C/ /ctx/ 
--
-- Set /A/ to \(B + C\).
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_add"
  fmpq_mpoly_add :: Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> Ptr CFmpqMPolyCtx -> IO ()

-- | /fmpq_mpoly_sub/ /A/ /B/ /C/ /ctx/ 
--
-- Set /A/ to \(B - C\).
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_sub"
  fmpq_mpoly_sub :: Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> Ptr CFmpqMPolyCtx -> IO ()

-- Scalar operations -----------------------------------------------------------

-- | /fmpq_mpoly_neg/ /A/ /B/ /ctx/ 
--
-- Set /A/ to \(-B\).
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_neg"
  fmpq_mpoly_neg :: Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> Ptr CFmpqMPolyCtx -> IO ()

-- | /fmpq_mpoly_scalar_mul_fmpq/ /A/ /B/ /c/ /ctx/ 
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_scalar_mul_fmpq"
  fmpq_mpoly_scalar_mul_fmpq :: Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> Ptr CFmpq -> Ptr CFmpqMPolyCtx -> IO ()
-- | /fmpq_mpoly_scalar_mul_fmpz/ /A/ /B/ /c/ /ctx/ 
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_scalar_mul_fmpz"
  fmpq_mpoly_scalar_mul_fmpz :: Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> Ptr CFmpz -> Ptr CFmpqMPolyCtx -> IO ()
-- | /fmpq_mpoly_scalar_mul_ui/ /A/ /B/ /c/ /ctx/ 
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_scalar_mul_ui"
  fmpq_mpoly_scalar_mul_ui :: Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> CULong -> Ptr CFmpqMPolyCtx -> IO ()
-- | /fmpq_mpoly_scalar_mul_si/ /A/ /B/ /c/ /ctx/ 
--
-- Set /A/ to \(B \times c\).
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_scalar_mul_si"
  fmpq_mpoly_scalar_mul_si :: Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> CLong -> Ptr CFmpqMPolyCtx -> IO ()

-- | /fmpq_mpoly_scalar_div_fmpq/ /A/ /B/ /c/ /ctx/ 
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_scalar_div_fmpq"
  fmpq_mpoly_scalar_div_fmpq :: Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> Ptr CFmpq -> Ptr CFmpqMPolyCtx -> IO ()
-- | /fmpq_mpoly_scalar_div_fmpz/ /A/ /B/ /c/ /ctx/ 
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_scalar_div_fmpz"
  fmpq_mpoly_scalar_div_fmpz :: Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> Ptr CFmpz -> Ptr CFmpqMPolyCtx -> IO ()
-- | /fmpq_mpoly_scalar_div_ui/ /A/ /B/ /c/ /ctx/ 
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_scalar_div_ui"
  fmpq_mpoly_scalar_div_ui :: Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> CULong -> Ptr CFmpqMPolyCtx -> IO ()
-- | /fmpq_mpoly_scalar_div_si/ /A/ /B/ /c/ /ctx/ 
--
-- Set /A/ to \(B/c\).
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_scalar_div_si"
  fmpq_mpoly_scalar_div_si :: Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> CLong -> Ptr CFmpqMPolyCtx -> IO ()

-- | /fmpq_mpoly_make_monic/ /A/ /B/ /ctx/ 
--
-- Set /A/ to /B/ divided by the leading coefficient of /B/. This throws if
-- /B/ is zero.
-- 
-- All of these functions run quickly if /A/ and /B/ are aliased.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_make_monic"
  fmpq_mpoly_make_monic :: Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> Ptr CFmpqMPolyCtx -> IO ()

-- Differentiation\/Integration ------------------------------------------------

-- | /fmpq_mpoly_derivative/ /A/ /B/ /var/ /ctx/ 
--
-- Set /A/ to the derivative of /B/ with respect to the variable of index
-- /var/.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_derivative"
  fmpq_mpoly_derivative :: Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> CLong -> Ptr CFmpqMPolyCtx -> IO ()

-- | /fmpq_mpoly_integral/ /A/ /B/ /var/ /ctx/ 
--
-- Set /A/ to the integral with the fewest number of terms of /B/ with
-- respect to the variable of index /var/.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_integral"
  fmpq_mpoly_integral :: Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> CLong -> Ptr CFmpqMPolyCtx -> IO ()

-- Evaluation ------------------------------------------------------------------




-- | /fmpq_mpoly_evaluate_all_fmpq/ /ev/ /A/ /vals/ /ctx/ 
--
-- Set @ev@ to the evaluation of /A/ where the variables are replaced by
-- the corresponding elements of the array @vals@. Return \(1\) for success
-- and \(0\) for failure.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_evaluate_all_fmpq"
  fmpq_mpoly_evaluate_all_fmpq :: Ptr CFmpq -> Ptr CFmpqMPoly -> Ptr (Ptr CFmpq) -> Ptr CFmpqMPolyCtx -> IO CInt

-- | /fmpq_mpoly_evaluate_one_fmpq/ /A/ /B/ /var/ /val/ /ctx/ 
--
-- Set /A/ to the evaluation of /B/ where the variable of index /var/ is
-- replaced by @val@. Return \(1\) for success and \(0\) for failure.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_evaluate_one_fmpq"
  fmpq_mpoly_evaluate_one_fmpq :: Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> CLong -> Ptr CFmpq -> Ptr CFmpqMPolyCtx -> IO CInt

-- | /fmpq_mpoly_compose_fmpq_poly/ /A/ /B/ /C/ /ctxB/ 
--
-- Set /A/ to the evaluation of /B/ where the variables are replaced by the
-- corresponding elements of the array /C/. The context object of /B/ is
-- /ctxB/. Return \(1\) for success and \(0\) for failure.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_compose_fmpq_poly"
  fmpq_mpoly_compose_fmpq_poly :: Ptr CFmpqPoly -> Ptr CFmpqMPoly -> Ptr (Ptr (Ptr (Ptr CFmpqPoly))) -> Ptr CFmpqMPolyCtx -> IO CInt

-- | /fmpq_mpoly_compose_fmpq_mpoly/ /A/ /B/ /C/ /ctxB/ /ctxAC/ 
--
-- Set /A/ to the evaluation of /B/ where the variables are replaced by the
-- corresponding elements of the array /C/. Both /A/ and the elements of
-- /C/ have context object /ctxAC/, while /B/ has context object /ctxB/.
-- Neither /A/ nor /B/ is allowed to alias any other polynomial. Return
-- \(1\) for success and \(0\) for failure.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_compose_fmpq_mpoly"
  fmpq_mpoly_compose_fmpq_mpoly :: Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> Ptr (Ptr (Ptr CFmpqMPoly)) -> Ptr CFmpqMPolyCtx -> Ptr CFmpqMPolyCtx -> IO CInt

-- | /fmpq_mpoly_compose_fmpq_mpoly_gen/ /A/ /B/ /c/ /ctxB/ /ctxAC/ 
--
-- Set /A/ to the evaluation of /B/ where the variable of index /i/ in
-- /ctxB/ is replaced by the variable of index @c[i]@ in /ctxAC/. The
-- length of the array /C/ is the number of variables in /ctxB/. If any
-- @c[i]@ is negative, the corresponding variable of /B/ is replaced by
-- zero. Otherwise, it is expected that @c[i]@ is less than the number of
-- variables in /ctxAC/.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_compose_fmpq_mpoly_gen"
  fmpq_mpoly_compose_fmpq_mpoly_gen :: Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> Ptr CLong -> Ptr CFmpqMPolyCtx -> Ptr CFmpqMPolyCtx -> IO ()

-- Multiplication --------------------------------------------------------------

-- | /fmpq_mpoly_mul/ /A/ /B/ /C/ /ctx/ 
--
-- Set /A/ to \(B \times C\).
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_mul"
  fmpq_mpoly_mul :: Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> Ptr CFmpqMPolyCtx -> IO ()

-- Powering --------------------------------------------------------------------




-- | /fmpq_mpoly_pow_fmpz/ /A/ /B/ /k/ /ctx/ 
--
-- Set /A/ to /B/ raised to the /k/-th power. Return \(1\) for success and
-- \(0\) for failure.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_pow_fmpz"
  fmpq_mpoly_pow_fmpz :: Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> Ptr CFmpz -> Ptr CFmpqMPolyCtx -> IO CInt

-- | /fmpq_mpoly_pow_ui/ /A/ /B/ /k/ /ctx/ 
--
-- Set /A/ to /B/ raised to the /k/-th power. Return \(1\) for success and
-- \(0\) for failure.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_pow_ui"
  fmpq_mpoly_pow_ui :: Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> CULong -> Ptr CFmpqMPolyCtx -> IO CInt

-- Division --------------------------------------------------------------------

-- | /fmpq_mpoly_divides/ /Q/ /A/ /B/ /ctx/ 
--
-- If /A/ is divisible by /B/, set /Q/ to the exact quotient and return
-- \(1\). Otherwise, set /Q/ to zero and return \(0\). Note that the
-- function @fmpq_mpoly_div@ may be faster if the quotient is known to be
-- exact.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_divides"
  fmpq_mpoly_divides :: Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> Ptr CFmpqMPolyCtx -> IO CInt

-- | /fmpq_mpoly_div/ /Q/ /A/ /B/ /ctx/ 
--
-- Set /Q/ to the quotient of /A/ by /B/, discarding the remainder.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_div"
  fmpq_mpoly_div :: Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> Ptr CFmpqMPolyCtx -> IO ()

-- | /fmpq_mpoly_divrem/ /Q/ /R/ /A/ /B/ /ctx/ 
--
-- Set /Q/ and /R/ to the quotient and remainder of /A/ divided by /B/.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_divrem"
  fmpq_mpoly_divrem :: Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> Ptr CFmpqMPolyCtx -> IO ()

-- | /fmpq_mpoly_divrem_ideal/ /Q/ /R/ /A/ /B/ /len/ /ctx/ 
--
-- This function is as per @fmpq_mpoly_divrem@ except that it takes an
-- array of divisor polynomials /B/ and it returns an array of quotient
-- polynomials /Q/. The number of divisor (and hence quotient) polynomials
-- is given by /len/.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_divrem_ideal"
  fmpq_mpoly_divrem_ideal :: Ptr (Ptr (Ptr CFmpqMPoly)) -> Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> Ptr (Ptr (Ptr CFmpqMPoly)) -> CLong -> Ptr CFmpqMPolyCtx -> IO ()

-- Greatest Common Divisor -----------------------------------------------------

-- | /fmpq_mpoly_content/ /g/ /A/ /ctx/ 
--
-- Set /g/ to the (nonnegative) gcd of the coefficients of /A/.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_content"
  fmpq_mpoly_content :: Ptr CFmpq -> Ptr CFmpqMPoly -> Ptr CFmpqMPolyCtx -> IO ()

-- | /fmpq_mpoly_term_content/ /M/ /A/ /ctx/ 
--
-- Set /M/ to the GCD of the terms of /A/. If /A/ is zero, /M/ will be
-- zero. Otherwise, /M/ will be a monomial with coefficient one.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_term_content"
  fmpq_mpoly_term_content :: Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> Ptr CFmpqMPolyCtx -> IO ()

-- | /fmpq_mpoly_content_vars/ /g/ /A/ /vars/ /vars_length/ /ctx/ 
--
-- Set /g/ to the GCD of the coefficients of /A/ when viewed as a
-- polynomial in the variables /vars/. Return \(1\) for success and \(0\)
-- for failure. Upon success, /g/ will be independent of the variables
-- /vars/.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_content_vars"
  fmpq_mpoly_content_vars :: Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> Ptr CLong -> CLong -> Ptr CFmpqMPolyCtx -> IO CInt

-- | /fmpq_mpoly_gcd/ /G/ /A/ /B/ /ctx/ 
--
-- Try to set /G/ to the monic GCD of /A/ and /B/. The GCD of zero and zero
-- is defined to be zero. If the return is \(1\) the function was
-- successful. Otherwise the return is \(0\) and /G/ is left untouched.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_gcd"
  fmpq_mpoly_gcd :: Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> Ptr CFmpqMPolyCtx -> IO CInt

-- | /fmpq_mpoly_gcd_cofactors/ /G/ /Abar/ /Bbar/ /A/ /B/ /ctx/ 
--
-- Do the operation of @fmpq_mpoly_gcd@ and also compute \(Abar = A/G\) and
-- \(Bbar = B/G\) if successful.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_gcd_cofactors"
  fmpq_mpoly_gcd_cofactors :: Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> Ptr CFmpqMPolyCtx -> IO CInt

-- | /fmpq_mpoly_gcd_brown/ /G/ /A/ /B/ /ctx/ 
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_gcd_brown"
  fmpq_mpoly_gcd_brown :: Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> Ptr CFmpqMPolyCtx -> IO CInt
-- | /fmpq_mpoly_gcd_hensel/ /G/ /A/ /B/ /ctx/ 
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_gcd_hensel"
  fmpq_mpoly_gcd_hensel :: Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> Ptr CFmpqMPolyCtx -> IO CInt
-- | /fmpq_mpoly_gcd_subresultant/ /G/ /A/ /B/ /ctx/ 
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_gcd_subresultant"
  fmpq_mpoly_gcd_subresultant :: Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> Ptr CFmpqMPolyCtx -> IO CInt
-- | /fmpq_mpoly_gcd_zippel/ /G/ /A/ /B/ /ctx/ 
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_gcd_zippel"
  fmpq_mpoly_gcd_zippel :: Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> Ptr CFmpqMPolyCtx -> IO CInt
-- | /fmpq_mpoly_gcd_zippel2/ /G/ /A/ /B/ /ctx/ 
--
-- Try to set /G/ to the GCD of /A/ and /B/ using various algorithms.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_gcd_zippel2"
  fmpq_mpoly_gcd_zippel2 :: Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> Ptr CFmpqMPolyCtx -> IO CInt

-- | /fmpq_mpoly_resultant/ /R/ /A/ /B/ /var/ /ctx/ 
--
-- Try to set /R/ to the resultant of /A/ and /B/ with respect to the
-- variable of index /var/.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_resultant"
  fmpq_mpoly_resultant :: Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> CLong -> Ptr CFmpqMPolyCtx -> IO CInt

-- | /fmpq_mpoly_discriminant/ /D/ /A/ /var/ /ctx/ 
--
-- Try to set /D/ to the discriminant of /A/ with respect to the variable
-- of index /var/.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_discriminant"
  fmpq_mpoly_discriminant :: Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> CLong -> Ptr CFmpqMPolyCtx -> IO CInt

-- Square Root -----------------------------------------------------------------

-- | /fmpq_mpoly_sqrt/ /Q/ /A/ /ctx/ 
--
-- If /A/ is a perfect square return \(1\) and set /Q/ to the square root
-- with positive leading coefficient. Otherwise return \(0\) and set /Q/ to
-- zero.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_sqrt"
  fmpq_mpoly_sqrt :: Ptr CFmpqMPoly -> Ptr CFmpqMPoly -> Ptr CFmpqMPolyCtx -> IO CInt

-- | /fmpq_mpoly_is_square/ /A/ /ctx/ 
--
-- Return \(1\) if /A/ is a perfect square, otherwise return \(0\).
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_is_square"
  fmpq_mpoly_is_square :: Ptr CFmpqMPoly -> Ptr CFmpqMPolyCtx -> IO CInt

-- UniVariate Functions --------------------------------------------------------




-- | /fmpq_mpoly_univar_init/ /A/ /ctx/ 
--
-- Initialize /A/.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_univar_init"
  fmpq_mpoly_univar_init :: Ptr CFmpqMPolyUniVar -> Ptr CFmpqMPolyCtx -> IO ()

-- | /fmpq_mpoly_univar_clear/ /A/ /ctx/ 
--
-- Clear /A/.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_univar_clear"
  fmpq_mpoly_univar_clear :: Ptr CFmpqMPolyUniVar -> Ptr CFmpqMPolyCtx -> IO ()

foreign import ccall "fmpq_mpoly.h &fmpq_mpoly_univar_clear"
  p_fmpq_mpoly_univar_clear :: FunPtr (Ptr CFmpqMPolyUniVar -> Ptr CFmpqMPolyCtx -> IO ())

-- | /fmpq_mpoly_univar_swap/ /A/ /B/ /ctx/ 
--
-- Swap /A/ and /B/.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_univar_swap"
  fmpq_mpoly_univar_swap :: Ptr CFmpqMPolyUniVar -> Ptr CFmpqMPolyUniVar -> Ptr CFmpqMPolyCtx -> IO ()

-- | /fmpq_mpoly_to_univar/ /A/ /B/ /var/ /ctx/ 
--
-- Set /A/ to a univariate form of /B/ by pulling out the variable of index
-- /var/. The coefficients of /A/ will still belong to the content /ctx/
-- but will not depend on the variable of index /var/.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_to_univar"
  fmpq_mpoly_to_univar :: Ptr CFmpqMPolyUniVar -> Ptr CFmpqMPoly -> CLong -> Ptr CFmpqMPolyCtx -> IO ()

-- | /fmpq_mpoly_from_univar/ /A/ /B/ /var/ /ctx/ 
--
-- Set /A/ to the normal form of /B/ by putting in the variable of index
-- /var/. This function is undefined if the coefficients of /B/ depend on
-- the variable of index /var/.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_from_univar"
  fmpq_mpoly_from_univar :: Ptr CFmpqMPoly -> Ptr CFmpqMPolyUniVar -> CLong -> Ptr CFmpqMPolyCtx -> IO ()

-- | /fmpq_mpoly_univar_degree_fits_si/ /A/ /ctx/ 
--
-- Return \(1\) if the degree of /A/ with respect to the main variable fits
-- an @slong@. Otherwise, return \(0\).
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_univar_degree_fits_si"
  fmpq_mpoly_univar_degree_fits_si :: Ptr CFmpqMPolyUniVar -> Ptr CFmpqMPolyCtx -> IO CInt

-- | /fmpq_mpoly_univar_length/ /A/ /ctx/ 
--
-- Return the number of terms in /A/ with respect to the main variable.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_univar_length"
  fmpq_mpoly_univar_length :: Ptr CFmpqMPolyUniVar -> Ptr CFmpqMPolyCtx -> IO CLong

-- | /fmpq_mpoly_univar_get_term_exp_si/ /A/ /i/ /ctx/ 
--
-- Return the exponent of the term of index /i/ of /A/.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_univar_get_term_exp_si"
  fmpq_mpoly_univar_get_term_exp_si :: Ptr CFmpqMPolyUniVar -> CLong -> Ptr CFmpqMPolyCtx -> IO CLong

-- | /fmpq_mpoly_univar_get_term_coeff/ /c/ /A/ /i/ /ctx/ 
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_univar_get_term_coeff"
  fmpq_mpoly_univar_get_term_coeff :: Ptr CFmpqMPoly -> Ptr CFmpqMPolyUniVar -> CLong -> Ptr CFmpqMPolyCtx -> IO ()
-- | /fmpq_mpoly_univar_swap_term_coeff/ /c/ /A/ /i/ /ctx/ 
--
-- Set (resp. swap) /c/ to (resp. with) the coefficient of the term of
-- index /i/ of /A/.
foreign import ccall "fmpq_mpoly.h fmpq_mpoly_univar_swap_term_coeff"
  fmpq_mpoly_univar_swap_term_coeff :: Ptr CFmpqMPoly -> Ptr CFmpqMPolyUniVar -> CLong -> Ptr CFmpqMPolyCtx -> IO ()

