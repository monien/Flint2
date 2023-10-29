module Data.Number.Flint.Calcium.Ca.FFI (
  -- * Exact Numbers
    Ca (..)
  , CCa (..)
  , CaCtx (..)
  , CCaCtx (..)
  , newCa
  , withCa
  , newCaCtx
  , withCaCtx
  -- * Number objects
  -- * Context objects
  , ca_ctx_init
  , ca_ctx_clear
  , ca_ctx_print
  -- * Memory management for numbers
  , ca_init
  , ca_clear
  , ca_swap
  -- * Symbolic expressions
  , ca_get_fexpr
  , ca_set_fexpr
  -- * Print flags
  , CalciumPrintOption (..)
  -- 
  -- | The style of printed output is controlled a flag which can be
  --   set to any combination of the following flags:
  , ca_print_n
  , ca_print_repr
  , ca_print_field
  , ca_print_digits
  , ca_print_default
  , ca_print_debug
  -- $printflags
  
  -- * Print
  , ca_print
  , ca_fprint
  , ca_get_str
  , ca_printn
  -- * Special values
  , ca_zero
  , ca_one
  , ca_neg_one
  , ca_i
  , ca_neg_i
  , ca_pi
  , ca_pi_i
  , ca_euler
  , ca_unknown
  , ca_undefined
  , ca_uinf
  , ca_pos_inf
  , ca_neg_inf
  , ca_pos_i_inf
  , ca_neg_i_inf
  -- * Assignment and conversion
  , ca_set
  , ca_set_si
  , ca_set_ui
  , ca_set_fmpz
  , ca_set_fmpq
  , ca_set_d
  , ca_set_d_d
  , ca_transfer
  -- * Conversion of algebraic numbers
  , ca_set_qqbar
  , ca_get_fmpz
  , ca_get_fmpq
  , ca_get_qqbar
  , ca_can_evaluate_qqbar
  -- * Random generation
  , ca_randtest_rational
  , ca_randtest
  , ca_randtest_special
  , ca_randtest_same_nf
  -- * Representation properties
  -- $representation
  , ca_equal_repr
  , ca_cmp_repr
  , ca_hash_repr
  , ca_is_unknown
  , ca_is_special
  , ca_is_qq_elem
  , ca_is_qq_elem_zero
  , ca_is_qq_elem_one
  , ca_is_qq_elem_integer
  , ca_is_nf_elem
  , ca_is_cyclotomic_nf_elem
  , ca_is_generic_elem
  -- * Value predicates
  , ca_check_is_number
  , ca_check_is_zero
  , ca_check_is_one
  , ca_check_is_neg_one
  , ca_check_is_i
  , ca_check_is_neg_i
  , ca_check_is_algebraic
  , ca_check_is_rational
  , ca_check_is_integer
  , ca_check_is_real
  , ca_check_is_negative_real
  , ca_check_is_imaginary
  , ca_check_is_undefined
  , ca_check_is_infinity
  , ca_check_is_uinf
  , ca_check_is_signed_inf
  , ca_check_is_pos_inf
  , ca_check_is_neg_inf
  , ca_check_is_pos_i_inf
  , ca_check_is_neg_i_inf
  -- * Comparisons
  , ca_check_equal
  , ca_check_lt
  , ca_check_le
  , ca_check_gt
  , ca_check_ge
  -- * Field structure operations
  , ca_merge_fields
  , ca_condense_field
  , ca_is_gen_as_ext
  -- * Arithmetic
  , ca_neg
  , ca_add_fmpq
  , ca_add_fmpz
  , ca_add_ui
  , ca_add_si
  , ca_add
  , ca_sub_fmpq
  , ca_sub_fmpz
  , ca_sub_ui
  , ca_sub_si
  , ca_fmpq_sub
  , ca_fmpz_sub
  , ca_ui_sub
  , ca_si_sub
  , ca_sub
  , ca_mul_fmpq
  , ca_mul_fmpz
  , ca_mul_ui
  , ca_mul_si
  , ca_mul
  , ca_inv
  , ca_fmpq_div
  , ca_fmpz_div
  , ca_ui_div
  , ca_si_div
  , ca_div_fmpq
  , ca_div_fmpz
  , ca_div_ui
  , ca_div_si
  , ca_div
  , ca_dot
  , ca_fmpz_poly_evaluate
  , ca_fmpq_poly_evaluate
  , ca_fmpz_mpoly_evaluate_horner
--, ca_fmpz_mpoly_evaluate_iter
  , ca_fmpz_mpoly_evaluate
  , ca_fmpz_mpoly_q_evaluate
  , ca_fmpz_mpoly_q_evaluate_no_division_by_zero
  , ca_inv_no_division_by_zero
  -- * Powers and roots
  , ca_sqr
  , ca_pow_fmpq
  , ca_pow_fmpz
  , ca_pow_ui
  , ca_pow_si
  , ca_pow
  , ca_pow_si_arithmetic
  , ca_sqrt_inert
  , ca_sqrt_nofactor
  , ca_sqrt_factor
  , ca_sqrt
  , ca_sqrt_ui
  -- * Complex parts
  , ca_abs
  , ca_sgn
  , ca_csgn
  , ca_arg
  , ca_re
  , ca_im
  , ca_conj_deep
  , ca_conj_shallow
  , ca_conj
  , ca_floor
  , ca_ceil
  -- * Exponentials and logarithms
  , ca_exp
  , ca_log
  -- * Trigonometric functions
  , ca_sin_cos_exponential
  , ca_sin_cos_direct
  , ca_sin_cos_tangent
  , ca_sin_cos
  , ca_sin
  , ca_cos
  , ca_tan_sine_cosine
  , ca_tan_exponential
  , ca_tan_direct
  , ca_tan
  , ca_cot
  , ca_atan_logarithm
  , ca_atan_direct
  , ca_atan
  , ca_asin_logarithm
  , ca_acos_logarithm
  , ca_asin_direct
  , ca_acos_direct
  , ca_asin
  , ca_acos
  -- * Special functions
  , ca_gamma
  , ca_erf
  , ca_erfc
  , ca_erfi
  -- * Numerical evaluation
  , ca_get_acb_raw
  , ca_get_acb
  , ca_get_acb_accurate_parts
  , ca_get_decimal_str
  -- * Rewriting and simplification
  , ca_rewrite_complex_normal_form
  -- * Factorization
  , CaFactor (..)
  , CCaFactor (..)
  , newCaFactor
  , withCaFactor
  , ca_factor_init
  , ca_factor_clear
  , ca_factor_one
  , ca_factor_print
  , ca_factor_insert
  , ca_factor_get_ca
  , ca_factor
  -- * Factorization options
  --
  -- $factorization_options
  
  , ca_factor_poly_none
  , ca_factor_poly_content
  , ca_factor_poly_sqf
  , ca_factor_poly_full
  , ca_factor_zz_none
  , ca_factor_zz_smooth
  , ca_factor_zz_full
  -- * Context options
  --
  -- $context_options
  
  , ca_opt_verbose
  , ca_opt_print_flags
  , ca_opt_mpoly_ord
  , ca_opt_prec_limit
  , ca_opt_qqbar_deg_limit
  , ca_opt_low_prec
  , ca_opt_smooth_limit
  , ca_opt_lll_prec
  , ca_opt_pow_limit
  , ca_opt_use_groebner
  , ca_opt_groebner_length_limit
  , ca_opt_groebner_poly_length_limit
  , ca_opt_groebner_poly_bits_limit
  , ca_opt_vieta_limit
  , ca_opt_trig_form
  , ca_trig_direct
  , ca_trig_exponential
  , ca_trig_sine_cosine
  , ca_trig_tangent
  -- * Internal representation
  , _ca_make_field_element
  , _ca_make_fmpq
) where

-- Exact real and complex numbers ----------------------------------------------

import Foreign.Ptr
import Foreign.ForeignPtr
import Foreign.Storable
import Foreign.C.Types
import Foreign.C.String

import Data.Number.Flint.Flint

import Data.Number.Flint.Fmpz
import Data.Number.Flint.Fmpz.Poly
import Data.Number.Flint.Fmpz.MPoly
import Data.Number.Flint.Fmpz.MPoly.Q
import Data.Number.Flint.Fmpq
import Data.Number.Flint.Fmpq.Poly

import Data.Number.Flint.NF.QQbar

import Data.Number.Flint.Arb.Types
import Data.Number.Flint.Acb.Types

import Data.Number.Flint.Calcium

#include <flint/ca.h>

-- to be defined ---------------------------------------------------------------

data CFexpr
data CCaField

-- ca_t ------------------------------------------------------------------------

data Ca = Ca {-# UNPACK #-} !(ForeignPtr CCa)
type CCa = CFlint Ca

instance Storable CCa where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size ca_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment ca_t}
  peek = error "CCa.peek: Not defined"
  poke = error "CCa.poke: Not defined"

newCa ctx@(CaCtx fctx) = do
  x <- mallocForeignPtr
  withForeignPtr x $ \xp -> do
    withCaCtx ctx $ \ctxp -> do
      ca_init xp ctxp
    addForeignPtrFinalizerEnv p_ca_clear xp fctx
  return $ Ca x

{-# INLINE withCa #-}
withCa (Ca x) f = do
  withForeignPtr x $ \xp -> f xp >>= return . (Ca x,)

withNewCa ctx f = do
  x <- newCa ctx
  withCa x f
  
-- ca_factor -------------------------------------------------------------------

data CaFactor = CaFactor {-# UNPACK #-} !(ForeignPtr CCaFactor)
type CCaFactor = CFlint CaFactor

instance Storable CCaFactor where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size ca_factor_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment ca_factor_t}
  peek = error "CCaFactor.peek: Not defined"
  poke = error "CCaFactor.poke: Not defined"

newCaFactor ctx@(CaCtx fctx) = do
  x <- mallocForeignPtr
  withForeignPtr x $ \xp -> do
    withCaCtx ctx $ \ctxp -> do
      ca_factor_init xp ctxp
    addForeignPtrFinalizerEnv p_ca_factor_clear xp fctx
  return $ CaFactor x

{-# INLINE withCaFactor #-}
withCaFactor (CaFactor x) f = do
  withForeignPtr x $ \xp -> f xp >>= return . (CaFactor x,)

withNewCaFactor ctx f = do
  x <- newCaFactor ctx
  withCaCtx ctx $ \ctx -> do
    withCaFactor x $ \x -> do
      f x ctx

-- -- ca_field -------------------------------------------------------------------

-- data CaField = CaField {-# UNPACK #-} !(ForeignPtr CCaField)
-- type CCaField = CFlint CaField

-- instance Storable CCaField where
--   {-# INLINE sizeOf #-}
--   sizeOf _ = #{size ca_field_t}
--   {-# INLINE alignment #-}
--   alignment _ = #{alignment ca_field_t}
--   peek = error "CCaField.peek: Not defined"
--   poke = error "CCaField.poke: Not defined"

-- newCaField ctx@(CaCtx fctx) = do
--   x <- mallocForeignPtr
--   withForeignPtr x $ \xp -> do
--     withCaCtx ctx $ \ctxp -> do
--       ca_field_init xp ctxp
--     addForeignPtrFinalizerEnv p_ca_field_clear xp fctx
--   return $ CaField x

-- {-# INLINE withCaField #-}
-- withCaField (CaField x) f = do
--   withForeignPtr x $ \xp -> f xp >>= return . (CaField x,)

-- withNewCaField ctx f = do
--   x <- newCaField ctx
--   withCaCtx ctx $ \ctx -> do
--     withCaField x $ \x -> do
--       f x ctx
      
-- ca_ctx ----------------------------------------------------------------------

data CaCtx = CaCtx {-# UNPACK #-} !(ForeignPtr CCaCtx)
type CCaCtx = CFlint CaCtx

instance Storable CCaCtx where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size ca_ctx_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment ca_ctx_t}
  peek = error "CCaCtx.peek: Not defined"
  poke = error "CCaCtx.poke: Not defined"

newCaCtx = do
  ctx <- mallocForeignPtr
  withForeignPtr ctx $ \ctxp -> do
    ca_ctx_init ctxp
  addForeignPtrFinalizer p_ca_ctx_clear ctx
  return $ CaCtx ctx

withCaCtx (CaCtx x) f = do
  withForeignPtr x $ \xp -> f xp >>= return . (CaCtx x,)
  
--------------------------------------------------------------------------------

-- | /ca_ctx_init/ /ctx/ 
--
-- Initializes the context object /ctx/ for use. Any evaluation options
-- stored in the context object are set to default values.
foreign import ccall "ca.h ca_ctx_init"
  ca_ctx_init :: Ptr CCaCtx -> IO ()

-- | /ca_ctx_clear/ /ctx/ 
--
-- Clears the context object /ctx/, freeing any memory allocated
-- internally. This function should only be called after all @ca_t@
-- instances referring to this context have been cleared.
foreign import ccall "ca.h ca_ctx_clear"
  ca_ctx_clear :: Ptr CCaCtx -> IO ()

foreign import ccall "ca.h &ca_ctx_clear"
  p_ca_ctx_clear :: FunPtr (Ptr CCaCtx -> IO ())

-- | /ca_ctx_print/ /ctx/ 
--
-- Prints a description of the context /ctx/ to standard output. This will
-- give a complete listing of the cached fields in /ctx/.
foreign import ccall "ca.h ca_ctx_print"
  ca_ctx_print :: Ptr CCaCtx -> IO ()

-- Memory management for numbers -----------------------------------------------

-- | /ca_init/ /x/ /ctx/ 
--
-- Initializes the variable /x/ for use, associating it with the context
-- object /ctx/. The value of /x/ is set to the rational number 0.
foreign import ccall "ca.h ca_init"
  ca_init :: Ptr CCa -> Ptr CCaCtx -> IO ()

-- | /ca_clear/ /x/ /ctx/ 
--
-- Clears the variable /x/.
foreign import ccall "ca.h ca_clear"
  ca_clear :: Ptr CCa -> Ptr CCaCtx -> IO ()

foreign import ccall "ca.h &ca_clear"
  p_ca_clear :: FunPtr (Ptr CCa -> Ptr CCaCtx -> IO ())

-- | /ca_swap/ /x/ /y/ /ctx/ 
--
-- Efficiently swaps the variables /x/ and /y/.
foreign import ccall "ca.h ca_swap"
  ca_swap :: Ptr CCa -> Ptr CCa -> Ptr CCaCtx -> IO ()

-- Symbolic expressions --------------------------------------------------------

-- | /ca_get_fexpr/ /res/ /x/ /flags/ /ctx/ 
--
-- Sets /res/ to a symbolic expression representing /x/.
foreign import ccall "ca.h ca_get_fexpr"
  ca_get_fexpr :: Ptr CFexpr -> Ptr CCa -> CULong -> Ptr CCaCtx -> IO ()

-- | /ca_set_fexpr/ /res/ /expr/ /ctx/ 
--
-- Sets /res/ to the value represented by the symbolic expression /expr/.
-- Returns 1 on success and 0 on failure. This function essentially just
-- traverses the expression tree using @ca@ arithmetic; it does not provide
-- advanced symbolic evaluation. It is guaranteed to at least be able to
-- parse the output of @ca_get_fexpr@.
foreign import ccall "ca.h ca_set_fexpr"
  ca_set_fexpr :: Ptr CCa -> Ptr CFexpr -> Ptr CCaCtx -> IO CInt

-- Printing --------------------------------------------------------------------

-- newtype CalciumPrintOption = CalciumPrintOption {_CalciumPrintOption :: CULong}
--   deriving (Show, Eq)

type CalciumPrintOption = CULong

ca_print_n, ca_print_digits, ca_print_repr, ca_print_field, ca_print_default, ca_print_debug :: CalciumPrintOption

-- | /ca_print_n/
--
-- Print a decimal approximation of the number.
-- The approximation is guaranteed to be correctly rounded to within
-- one unit in the last place.
-- 
-- If combined with ``ca_print_repr``, numbers appearing
-- within the symbolic representation will also be printed with
-- decimal approximations.
--
-- Warning: printing a decimal approximation requires a computation,
-- which can be expensive. It can also mutate
-- cached data (numerical enclosures of extension numbers), affecting
-- subsequent computations.
ca_print_n       =  #const CA_PRINT_N 
-- | /ca_print_digits/
--
-- Multiplied by a positive integer, specifies the number of
-- decimal digits to show with ``ca_print_n``. If not given,
-- the default precision is six digits.
ca_print_digits  = #const CA_PRINT_DIGITS
-- | /ca_print_repr/
--
-- Print the symbolic representation of the number (including
-- its recursive elements). If used together with ``ca_print_n``,
-- field elements will print as ``decimal {symbolic}`` while
-- extension numbers will print as ``decimal [symbolic]``.
--
-- All extension numbers appearing in the field defining ``x``
-- and in the inner constructions of those extension numbers
-- will be given local labels ``a``, ``b``, etc. for this printing.
ca_print_repr    = #const CA_PRINT_REPR
-- | /ca_print_field/
--
-- For each field element, explicitly print its formal field
-- along with its reduction ideal if present, e.g. ``QQ`` or
-- ``QQ(a,b,c) / <a-b, c^2+1>``.
ca_print_field   = #const CA_PRINT_FIELD
-- | /ca_print_default/
--
-- The default print style. Equivalent to ``ca_print_n | ca_print_repr``.
ca_print_default = #const CA_PRINT_DEFAULT
-- | /ca_print_debug/
--
-- Verbose print style for debugging. Equivalent to ``ca_print_n |
-- ca_print_repr | ca_print_field``.
ca_print_debug   = #const CA_PRINT_DEBUG

-- $printflags
--
-- == Example for print flags
-- 
-- As a special case, small integers are always printed as simple literals.
--
-- As illustration, here are the numbers -7, \(2/3\), \((\sqrt{3}+5)/2\)
-- and \(\sqrt{2} (\log(\pi) + \pi i)\) printed in various styles:
--
-- >> ca_print_default
-- -7
-- 0.666667 {2/3}
-- 3.36603 {(a+5)/2 where a = 1.73205 [a^2-3=0]}
-- 1.61889 + 4.44288*I {a*c+b*c*d where a = 1.14473 [Log(3.14159 {b})], b = 3.14159 [Pi], c = 1.41421 [c^2-2=0], d = I [d^2+1=0]}
--
-- >> ca_print_n
-- -7
-- 0.666667
-- 3.36603
-- 1.61889 + 4.44288*I
--
-- >> ca_print_n .|. (ca_print_digits * 20)
-- -7
-- 0.66666666666666666667
-- 3.3660254037844386468
-- 1.6188925298220266685 + 4.4428829381583662470*I
--
-- >> ca_print_repr
-- -7
-- 2/3
-- (a+5)/2 where a = [a^2-3=0]
-- a*c+b*c*d where a = Log(b), b = Pi, c = [c^2-2=0], d = [d^2+1=0]
--
-- >> ca_print_debug
-- -7
-- 0.666667 {2/3  in  QQ}
-- 3.36603 {(a+5)/2  in  QQ(a)/<a^2-3> where a = 1.73205 [a^2-3=0]}
-- 1.61889 + 4.44288*I {a*c+b*c*d  in  QQ(a,b,c,d)/<c^2-2, d^2+1> where a = 1.14473 [Log(3.14159 {b  in  QQ(b)})], b = 3.14159 [Pi], c = 1.41421 [c^2-2=0], d = I [d^2+1=0]}

-- | /ca_print/ /x/ /ctx/ 
--
-- Prints /x/ to standard output.
ca_print :: Ptr CCa -> Ptr CCaCtx -> IO ()
ca_print x ctx = do
  printCStr (\x -> ca_get_str x ctx) x
  return ()
  
-- | /ca_fprint/ /fp/ /x/ /ctx/ 
--
-- Prints /x/ to the file /fp/.
foreign import ccall "ca.h ca_fprint"
  ca_fprint :: Ptr CFile -> Ptr CCa -> Ptr CCaCtx -> IO ()

-- | /ca_get_str/ /x/ /ctx/ 
--
-- Prints /x/ to a string which is returned. The user should free this
-- string by calling @flint_free@.
foreign import ccall "ca.h ca_get_str"
  ca_get_str :: Ptr CCa -> Ptr CCaCtx -> IO CString

-- | /ca_printn/ /x/ /n/ /ctx/ 
--
-- Prints an /n/-digit numerical representation of /x/ to standard output.
foreign import ccall "ca.h ca_printn"
  ca_printn :: Ptr CCa -> CLong -> Ptr CCaCtx -> IO ()

-- Special values --------------------------------------------------------------

-- | /ca_zero/ /res/ /ctx/ 
foreign import ccall "ca.h ca_zero"
  ca_zero :: Ptr CCa -> Ptr CCaCtx -> IO ()
-- | /ca_one/ /res/ /ctx/ 
foreign import ccall "ca.h ca_one"
  ca_one :: Ptr CCa -> Ptr CCaCtx -> IO ()
-- | /ca_neg_one/ /res/ /ctx/ 
--
-- Sets /res/ to the integer 0, 1 or -1. This creates a canonical
-- representation of this number as an element of the trivial field
-- \(\mathbb{Q}\).
foreign import ccall "ca.h ca_neg_one"
  ca_neg_one :: Ptr CCa -> Ptr CCaCtx -> IO ()

-- | /ca_i/ /res/ /ctx/ 
foreign import ccall "ca.h ca_i"
  ca_i :: Ptr CCa -> Ptr CCaCtx -> IO ()
-- | /ca_neg_i/ /res/ /ctx/ 
--
-- Sets /res/ to the imaginary unit \(i = \sqrt{-1}\), or its negation
-- \(-i\). This creates a canonical representation of \(i\) as the
-- generator of the algebraic number field \(\mathbb{Q}(i)\).
foreign import ccall "ca.h ca_neg_i"
  ca_neg_i :: Ptr CCa -> Ptr CCaCtx -> IO ()

-- | /ca_pi/ /res/ /ctx/ 
--
-- Sets /res/ to the constant \(\pi\). This creates an element of the
-- transcendental number field \(\mathbb{Q}(\pi)\).
foreign import ccall "ca.h ca_pi"
  ca_pi :: Ptr CCa -> Ptr CCaCtx -> IO ()

-- | /ca_pi_i/ /res/ /ctx/ 
--
-- Sets /res/ to the constant \(\pi i\). This creates an element of the
-- composite field \(\mathbb{Q}(i,\pi)\) rather than representing \(\pi i\)
-- (or even \(2 \pi i\), which for some purposes would be more elegant) as
-- an atomic quantity.
foreign import ccall "ca.h ca_pi_i"
  ca_pi_i :: Ptr CCa -> Ptr CCaCtx -> IO ()

-- | /ca_euler/ /res/ /ctx/ 
--
-- Sets /res/ to Euler\'s constant \(\gamma\). This creates an element of
-- the (transcendental?) number field \(\mathbb{Q}(\gamma)\).
foreign import ccall "ca.h ca_euler"
  ca_euler :: Ptr CCa -> Ptr CCaCtx -> IO ()

-- | /ca_unknown/ /res/ /ctx/ 
--
-- Sets /res/ to the meta-value /Unknown/.
foreign import ccall "ca.h ca_unknown"
  ca_unknown :: Ptr CCa -> Ptr CCaCtx -> IO ()

-- | /ca_undefined/ /res/ /ctx/ 
--
-- Sets /res/ to /Undefined/.
foreign import ccall "ca.h ca_undefined"
  ca_undefined :: Ptr CCa -> Ptr CCaCtx -> IO ()

-- | /ca_uinf/ /res/ /ctx/ 
--
-- Sets /res/ to unsigned infinity \({\tilde \infty}\).
foreign import ccall "ca.h ca_uinf"
  ca_uinf :: Ptr CCa -> Ptr CCaCtx -> IO ()

-- | /ca_pos_inf/ /res/ /ctx/ 
foreign import ccall "ca.h ca_pos_inf"
  ca_pos_inf :: Ptr CCa -> Ptr CCaCtx -> IO ()
  
-- | /ca_neg_inf/ /res/ /ctx/ 
foreign import ccall "ca.h ca_neg_inf"
  ca_neg_inf :: Ptr CCa -> Ptr CCaCtx -> IO ()
  
-- | /ca_pos_i_inf/ /res/ /ctx/ 
foreign import ccall "ca.h ca_pos_i_inf"
  ca_pos_i_inf :: Ptr CCa -> Ptr CCaCtx -> IO ()
  
-- | /ca_neg_i_inf/ /res/ /ctx/ 
--
-- Sets /res/ to the signed infinity \(+\infty\), \(-\infty\),
-- \(+i \infty\) or \(-i \infty\).
foreign import ccall "ca.h ca_neg_i_inf"
  ca_neg_i_inf :: Ptr CCa -> Ptr CCaCtx -> IO ()

-- Assignment and conversion ---------------------------------------------------

-- | /ca_set/ /res/ /x/ /ctx/ 
--
-- Sets /res/ to a copy of /x/.
foreign import ccall "ca.h ca_set"
  ca_set :: Ptr CCa -> Ptr CCa -> Ptr CCaCtx -> IO ()

-- | /ca_set_si/ /res/ /v/ /ctx/ 
foreign import ccall "ca.h ca_set_si"
  ca_set_si :: Ptr CCa -> CLong -> Ptr CCaCtx -> IO ()
-- | /ca_set_ui/ /res/ /v/ /ctx/ 
foreign import ccall "ca.h ca_set_ui"
  ca_set_ui :: Ptr CCa -> CULong -> Ptr CCaCtx -> IO ()
-- | /ca_set_fmpz/ /res/ /v/ /ctx/ 
foreign import ccall "ca.h ca_set_fmpz"
  ca_set_fmpz :: Ptr CCa -> Ptr CFmpz -> Ptr CCaCtx -> IO ()
-- | /ca_set_fmpq/ /res/ /v/ /ctx/ 
--
-- Sets /res/ to the integer or rational number /v/. This creates a
-- canonical representation of this number as an element of the trivial
-- field \(\mathbb{Q}\).
foreign import ccall "ca.h ca_set_fmpq"
  ca_set_fmpq :: Ptr CCa -> Ptr CFmpq -> Ptr CCaCtx -> IO ()

-- | /ca_set_d/ /res/ /x/ /ctx/ 
foreign import ccall "ca.h ca_set_d"
  ca_set_d :: Ptr CCa -> CDouble -> Ptr CCaCtx -> IO ()
-- | /ca_set_d_d/ /res/ /x/ /y/ /ctx/ 
--
-- Sets /res/ to the value of /x/, or the complex value \(x + yi\). NaN is
-- interpreted as /Unknown/ (not /Undefined/).
foreign import ccall "ca.h ca_set_d_d"
  ca_set_d_d :: Ptr CCa -> CDouble -> CDouble -> Ptr CCaCtx -> IO ()

-- | /ca_transfer/ /res/ /res_ctx/ /src/ /src_ctx/ 
--
-- Sets /res/ to /src/ where the corresponding context objects /res_ctx/
-- and /src_ctx/ may be different.
-- 
-- This operation preserves the mathematical value represented by /src/,
-- but may result in a different internal representation depending on the
-- settings of the context objects.
foreign import ccall "ca.h ca_transfer"
  ca_transfer :: Ptr CCa -> Ptr CCaCtx -> Ptr CCa -> Ptr CCaCtx -> IO ()

-- Conversion of algebraic numbers ---------------------------------------------

-- | /ca_set_qqbar/ /res/ /x/ /ctx/ 
--
-- Sets /res/ to the algebraic number /x/.
-- 
-- If /x/ is rational, /res/ is set to the canonical representation as an
-- element in the trivial field \(\mathbb{Q}\).
-- 
-- If /x/ is irrational, this function always sets /res/ to an element of a
-- univariate number field \(\mathbb{Q}(a)\). It will not, for example,
-- identify \(\sqrt{2} + \sqrt{3}\) as an element of
-- \(\mathbb{Q}(\sqrt{2}, \sqrt{3})\). However, it may attempt to find a
-- simpler number field than that generated by /x/ itself. For example:
-- 
-- -   If /x/ is quadratic, it will be expressed as an element of
--     \(\mathbb{Q}(\sqrt{N})\) where /N/ has no small repeated factors
--     (obtained by performing a smooth factorization of the discriminant).
-- -   TODO: if possible, coerce /x/ to a low-degree cyclotomic field.
foreign import ccall "ca.h ca_set_qqbar"
  ca_set_qqbar :: Ptr CCa -> Ptr CQQbar -> Ptr CCaCtx -> IO ()

-- | /ca_get_fmpz/ /res/ /x/ /ctx/ 
foreign import ccall "ca.h ca_get_fmpz"
  ca_get_fmpz :: Ptr CFmpz -> Ptr CCa -> Ptr CCaCtx -> IO CInt
  
-- | /ca_get_fmpq/ /res/ /x/ /ctx/ 
foreign import ccall "ca.h ca_get_fmpq"
  ca_get_fmpq :: Ptr CFmpq -> Ptr CCa -> Ptr CCaCtx -> IO CInt
  
-- | /ca_get_qqbar/ /res/ /x/ /ctx/ 
--
-- Attempts to evaluate /x/ to an explicit integer, rational or algebraic
-- number. If successful, sets /res/ to this number and returns 1. If
-- unsuccessful, returns 0.
-- 
-- The conversion certainly fails if /x/ does not represent an integer,
-- rational or algebraic number (respectively), but can also fail if /x/ is
-- too expensive to compute under the current evaluation limits. In
-- particular, the evaluation will be aborted if an intermediate algebraic
-- number (or more precisely, the resultant polynomial prior to
-- factorization) exceeds @CA_OPT_QQBAR_DEG_LIMIT@ or the coefficients
-- exceed some multiple of @CA_OPT_PREC_LIMIT@. Note that evaluation may
-- hit those limits even if the minimal polynomial for /x/ itself is small.
-- The conversion can also fail if no algorithm has been implemented for
-- the functions appearing in the construction of /x/.
foreign import ccall "ca.h ca_get_qqbar"
  ca_get_qqbar :: Ptr CQQbar -> Ptr CCa -> Ptr CCaCtx -> IO CInt

-- | /ca_can_evaluate_qqbar/ /x/ /ctx/ 
--
-- Checks if @ca_get_qqbar@ has a chance to succeed. In effect, this checks
-- if all extension numbers are manifestly algebraic numbers (without doing
-- any evaluation).
foreign import ccall "ca.h ca_can_evaluate_qqbar"
  ca_can_evaluate_qqbar :: Ptr CCa -> Ptr CCaCtx -> IO CInt

-- Random generation -----------------------------------------------------------

-- | /ca_randtest_rational/ /res/ /state/ /bits/ /ctx/ 
--
-- Sets /res/ to a random rational number with numerator and denominator up
-- to /bits/ bits in size.
foreign import ccall "ca.h ca_randtest_rational"
  ca_randtest_rational :: Ptr CCa -> Ptr CFRandState -> CLong -> Ptr CCaCtx -> IO ()

-- | /ca_randtest/ /res/ /state/ /depth/ /bits/ /ctx/ 
--
-- Sets /res/ to a random number generated by evaluating a random
-- expression. The algorithm randomly selects between generating a
-- \"simple\" number (a random rational number or quadratic field element
-- with coefficients up to /bits/ in size, or a random builtin constant),
-- or if /depth/ is nonzero, applying a random arithmetic operation or
-- function to operands produced through recursive calls with /depth/ - 1.
-- The output is guaranteed to be a number, not a special value.
foreign import ccall "ca.h ca_randtest"
  ca_randtest :: Ptr CCa -> Ptr CFRandState -> CLong -> CLong -> Ptr CCaCtx -> IO ()

-- | /ca_randtest_special/ /res/ /state/ /depth/ /bits/ /ctx/ 
--
-- Randomly generates either a special value or a number.
foreign import ccall "ca.h ca_randtest_special"
  ca_randtest_special :: Ptr CCa -> Ptr CFRandState -> CLong -> CLong -> Ptr CCaCtx -> IO ()

-- | /ca_randtest_same_nf/ /res/ /state/ /x/ /bits/ /den_bits/ /ctx/ 
--
-- Sets /res/ to a random element in the same number field as /x/, with
-- numerator coefficients up to /bits/ in size and denominator up to
-- /den_bits/ in size. This function requires that /x/ is an element of an
-- absolute number field.
foreign import ccall "ca.h ca_randtest_same_nf"
  ca_randtest_same_nf :: Ptr CCa -> Ptr CFRandState -> Ptr CCa -> CLong -> CLong -> Ptr CCaCtx -> IO ()

-- $representation
--
-- The following functions deal with the representation of a @Ca@ and
-- hence can always be decided quickly and unambiguously. The return value
-- for predicates is 0 for false and 1 for true.

-- | /ca_equal_repr/ /x/ /y/ /ctx/ 
--
-- Returns whether /x/ and /y/ have identical representation. For field
-- elements, this checks if /x/ and /y/ belong to the same formal field
-- (with generators having identical representation) and are represented by
-- the same rational function within that field.
-- 
-- For special values, this tests equality of the special values, with
-- /Unknown/ handled as if it were a value rather than a meta-value: that
-- is, /Unknown/ = /Unknown/ gives 1, and /Unknown/ = /y/ gives 0 for any
-- other kind of value /y/. If neither /x/ nor /y/ is /Unknown/, then
-- representation equality implies that /x/ and /y/ describe to the same
-- mathematical value, but if either operand is /Unknown/, the result is
-- meaningless for mathematical comparison.
foreign import ccall "ca.h ca_equal_repr"
  ca_equal_repr :: Ptr CCa -> Ptr CCa -> Ptr CCaCtx -> IO CInt

-- | /ca_cmp_repr/ /x/ /y/ /ctx/ 
--
-- Compares the representations of /x/ and /y/ in a canonical sort order,
-- returning -1, 0 or 1. This only performs a lexicographic comparison of
-- the representations of /x/ and /y/; the return value does not say
-- anything meaningful about the numbers represented by /x/ and /y/.
foreign import ccall "ca.h ca_cmp_repr"
  ca_cmp_repr :: Ptr CCa -> Ptr CCa -> Ptr CCaCtx -> IO CInt

-- | /ca_hash_repr/ /x/ /ctx/ 
--
-- Hashes the representation of /x/.
foreign import ccall "ca.h ca_hash_repr"
  ca_hash_repr :: Ptr CCa -> Ptr CCaCtx -> IO CULong

-- | /ca_is_unknown/ /x/ /ctx/ 
--
-- Returns whether /x/ is Unknown.
foreign import ccall "ca.h ca_is_unknown"
  ca_is_unknown :: Ptr CCa -> Ptr CCaCtx -> IO CInt

-- | /ca_is_special/ /x/ /ctx/ 
--
-- Returns whether /x/ is a special value or metavalue (not a field
-- element).
foreign import ccall "ca.h ca_is_special"
  ca_is_special :: Ptr CCa -> Ptr CCaCtx -> IO CInt

-- | /ca_is_qq_elem/ /x/ /ctx/ 
--
-- Returns whether /x/ is represented as an element of the rational field
-- \(\mathbb{Q}\).
foreign import ccall "ca.h ca_is_qq_elem"
  ca_is_qq_elem :: Ptr CCa -> Ptr CCaCtx -> IO CInt

-- | /ca_is_qq_elem_zero/ /x/ /ctx/ 
foreign import ccall "ca.h ca_is_qq_elem_zero"
  ca_is_qq_elem_zero :: Ptr CCa -> Ptr CCaCtx -> IO CInt
-- | /ca_is_qq_elem_one/ /x/ /ctx/ 
foreign import ccall "ca.h ca_is_qq_elem_one"
  ca_is_qq_elem_one :: Ptr CCa -> Ptr CCaCtx -> IO CInt
-- | /ca_is_qq_elem_integer/ /x/ /ctx/ 
--
-- Returns whether /x/ is represented as the element 0, 1 or any integer in
-- the rational field \(\mathbb{Q}\).
foreign import ccall "ca.h ca_is_qq_elem_integer"
  ca_is_qq_elem_integer :: Ptr CCa -> Ptr CCaCtx -> IO CInt

-- | /ca_is_nf_elem/ /x/ /ctx/ 
--
-- Returns whether /x/ is represented as an element of a univariate
-- algebraic number field \(\mathbb{Q}(a)\).
foreign import ccall "ca.h ca_is_nf_elem"
  ca_is_nf_elem :: Ptr CCa -> Ptr CCaCtx -> IO CInt

-- | /ca_is_cyclotomic_nf_elem/ /p/ /q/ /x/ /ctx/ 
--
-- Returns whether /x/ is represented as an element of a univariate
-- cyclotomic field, i.e. \(\mathbb{Q}(a)\) where /a/ is a root of unity.
-- If /p/ and /q/ are not /NULL/ and /x/ is represented as an element of a
-- cyclotomic field, this also sets /p/ and /q/ to the minimal integers
-- with \(0 \le p < q\) such that the generating root of unity is
-- \(a = e^{2 \pi i p / q}\). Note that the answer 0 does not prove that
-- /x/ is not a cyclotomic number, and the order /q/ is also not
-- necessarily the generator of the /smallest/ cyclotomic field containing
-- /x/. For the purposes of this function, only nontrivial cyclotomic
-- fields count; the return value is 0 if /x/ is represented as a rational
-- number.
foreign import ccall "ca.h ca_is_cyclotomic_nf_elem"
  ca_is_cyclotomic_nf_elem :: Ptr CLong -> Ptr CULong -> Ptr CCa -> Ptr CCaCtx -> IO CInt

-- | /ca_is_generic_elem/ /x/ /ctx/ 
--
-- Returns whether /x/ is represented as a generic field element; i.e. it
-- is not a special value, not represented as an element of the rational
-- field, and not represented as an element of a univariate algebraic
-- number field.
foreign import ccall "ca.h ca_is_generic_elem"
  ca_is_generic_elem :: Ptr CCa -> Ptr CCaCtx -> IO CInt

-- Value predicates ------------------------------------------------------------

-- The following predicates check a mathematical property which might not
-- be effectively decidable. The result is a @truth_t@ to allow
-- representing an unknown outcome.
--
-- | /ca_check_is_number/ /x/ /ctx/ 
--
-- Tests if /x/ is a number. The result is @T_TRUE@ is /x/ is a field
-- element (and hence a complex number), @T_FALSE@ if /x/ is an infinity or
-- /Undefined/, and @T_UNKNOWN@ if /x/ is /Unknown/.
foreign import ccall "ca.h ca_check_is_number"
  ca_check_is_number :: Ptr CCa -> Ptr CCaCtx -> IO (Ptr CTruth)

-- | /ca_check_is_zero/ /x/ /ctx/ 
foreign import ccall "ca.h ca_check_is_zero"
  ca_check_is_zero :: Ptr CCa -> Ptr CCaCtx -> IO (Ptr CTruth)
-- | /ca_check_is_one/ /x/ /ctx/ 
foreign import ccall "ca.h ca_check_is_one"
  ca_check_is_one :: Ptr CCa -> Ptr CCaCtx -> IO (Ptr CTruth)
-- | /ca_check_is_neg_one/ /x/ /ctx/ 
foreign import ccall "ca.h ca_check_is_neg_one"
  ca_check_is_neg_one :: Ptr CCa -> Ptr CCaCtx -> IO (Ptr CTruth)
-- | /ca_check_is_i/ /x/ /ctx/ 
foreign import ccall "ca.h ca_check_is_i"
  ca_check_is_i :: Ptr CCa -> Ptr CCaCtx -> IO (Ptr CTruth)
-- | /ca_check_is_neg_i/ /x/ /ctx/ 
--
-- Tests if /x/ is equal to the number \(0\), \(1\), \(-1\), \(i\), or
-- \(-i\).
foreign import ccall "ca.h ca_check_is_neg_i"
  ca_check_is_neg_i :: Ptr CCa -> Ptr CCaCtx -> IO (Ptr CTruth)

-- | /ca_check_is_algebraic/ /x/ /ctx/ 
foreign import ccall "ca.h ca_check_is_algebraic"
  ca_check_is_algebraic :: Ptr CCa -> Ptr CCaCtx -> IO (Ptr CTruth)
-- | /ca_check_is_rational/ /x/ /ctx/ 
foreign import ccall "ca.h ca_check_is_rational"
  ca_check_is_rational :: Ptr CCa -> Ptr CCaCtx -> IO (Ptr CTruth)
-- | /ca_check_is_integer/ /x/ /ctx/ 
--
-- Tests if /x/ is respectively an algebraic number, a rational number, or
-- an integer.
foreign import ccall "ca.h ca_check_is_integer"
  ca_check_is_integer :: Ptr CCa -> Ptr CCaCtx -> IO (Ptr CTruth)

-- | /ca_check_is_real/ /x/ /ctx/ 
--
-- Tests if /x/ is a real number. Warning: this returns @T_FALSE@ if /x/ is
-- an infinity with real sign.
foreign import ccall "ca.h ca_check_is_real"
  ca_check_is_real :: Ptr CCa -> Ptr CCaCtx -> IO (Ptr CTruth)

-- | /ca_check_is_negative_real/ /x/ /ctx/ 
--
-- Tests if /x/ is a negative real number. Warning: this returns @T_FALSE@
-- if /x/ is negative infinity.
foreign import ccall "ca.h ca_check_is_negative_real"
  ca_check_is_negative_real :: Ptr CCa -> Ptr CCaCtx -> IO (Ptr CTruth)

-- | /ca_check_is_imaginary/ /x/ /ctx/ 
--
-- Tests if /x/ is an imaginary number. Warning: this returns @T_FALSE@ if
-- /x/ is an infinity with imaginary sign.
foreign import ccall "ca.h ca_check_is_imaginary"
  ca_check_is_imaginary :: Ptr CCa -> Ptr CCaCtx -> IO (Ptr CTruth)

-- | /ca_check_is_undefined/ /x/ /ctx/ 
--
-- Tests if /x/ is the special value /Undefined/.
foreign import ccall "ca.h ca_check_is_undefined"
  ca_check_is_undefined :: Ptr CCa -> Ptr CCaCtx -> IO (Ptr CTruth)

-- | /ca_check_is_infinity/ /x/ /ctx/ 
--
-- Tests if /x/ is any infinity (unsigned or signed).
foreign import ccall "ca.h ca_check_is_infinity"
  ca_check_is_infinity :: Ptr CCa -> Ptr CCaCtx -> IO (Ptr CTruth)

-- | /ca_check_is_uinf/ /x/ /ctx/ 
--
-- Tests if /x/ is unsigned infinity \({\tilde \infty}\).
foreign import ccall "ca.h ca_check_is_uinf"
  ca_check_is_uinf :: Ptr CCa -> Ptr CCaCtx -> IO (Ptr CTruth)

-- | /ca_check_is_signed_inf/ /x/ /ctx/ 
--
-- Tests if /x/ is any signed infinity.
foreign import ccall "ca.h ca_check_is_signed_inf"
  ca_check_is_signed_inf :: Ptr CCa -> Ptr CCaCtx -> IO (Ptr CTruth)

-- | /ca_check_is_pos_inf/ /x/ /ctx/ 
foreign import ccall "ca.h ca_check_is_pos_inf"
  ca_check_is_pos_inf :: Ptr CCa -> Ptr CCaCtx -> IO (Ptr CTruth)
-- | /ca_check_is_neg_inf/ /x/ /ctx/ 
foreign import ccall "ca.h ca_check_is_neg_inf"
  ca_check_is_neg_inf :: Ptr CCa -> Ptr CCaCtx -> IO (Ptr CTruth)
-- | /ca_check_is_pos_i_inf/ /x/ /ctx/ 
foreign import ccall "ca.h ca_check_is_pos_i_inf"
  ca_check_is_pos_i_inf :: Ptr CCa -> Ptr CCaCtx -> IO (Ptr CTruth)
-- | /ca_check_is_neg_i_inf/ /x/ /ctx/ 
--
-- Tests if /x/ is equal to the signed infinity \(+\infty\), \(-\infty\),
-- \(+i \infty\), \(-i \infty\), respectively.
foreign import ccall "ca.h ca_check_is_neg_i_inf"
  ca_check_is_neg_i_inf :: Ptr CCa -> Ptr CCaCtx -> IO (Ptr CTruth)

-- Comparisons -----------------------------------------------------------------

-- | /ca_check_equal/ /x/ /y/ /ctx/ 
--
-- Tests \(x = y\) as a mathematical equality. The result is @T_UNKNOWN@ if
-- either operand is /Unknown/. The result may also be @T_UNKNOWN@ if /x/
-- and /y/ are numerically indistinguishable and cannot be proved equal or
-- unequal by an exact computation.
foreign import ccall "ca.h ca_check_equal"
  ca_check_equal :: Ptr CCa -> Ptr CCa -> Ptr CCaCtx -> IO (Ptr CTruth)

-- | /ca_check_lt/ /x/ /y/ /ctx/ 
foreign import ccall "ca.h ca_check_lt"
  ca_check_lt :: Ptr CCa -> Ptr CCa -> Ptr CCaCtx -> IO (Ptr CTruth)
  
-- | /ca_check_le/ /x/ /y/ /ctx/ 
foreign import ccall "ca.h ca_check_le"
  ca_check_le :: Ptr CCa -> Ptr CCa -> Ptr CCaCtx -> IO (Ptr CTruth)
  
-- | /ca_check_gt/ /x/ /y/ /ctx/ 
foreign import ccall "ca.h ca_check_gt"
  ca_check_gt :: Ptr CCa -> Ptr CCa -> Ptr CCaCtx -> IO (Ptr CTruth)
-- | /ca_check_ge/ /x/ /y/ /ctx/ 
--
-- Compares /x/ and /y/, implementing the respective operations \(x < y\),
-- \(x \le y\), \(x > y\), \(x \ge y\). Only real numbers and \(-\infty\)
-- and \(+\infty\) are considered comparable. The result is @T_FALSE@ (not
-- @T_UNKNOWN@) if either operand is not comparable (being a nonreal
-- complex number, unsigned infinity, or undefined).
foreign import ccall "ca.h ca_check_ge"
  ca_check_ge :: Ptr CCa -> Ptr CCa -> Ptr CCaCtx -> IO (Ptr CTruth)

-- Field structure operations --------------------------------------------------

-- | /ca_merge_fields/ /resx/ /resy/ /x/ /y/ /ctx/ 
--
-- Sets /resx/ and /resy/ to copies of /x/ and /y/ coerced to a common
-- field. Both /x/ and /y/ must be field elements (not special values).
-- 
-- In the present implementation, this simply merges the lists of
-- generators, avoiding duplication. In the future, it will be able to
-- eliminate generators satisfying algebraic relations.
foreign import ccall "ca.h ca_merge_fields"
  ca_merge_fields :: Ptr CCa -> Ptr CCa -> Ptr CCa -> Ptr CCa -> Ptr CCaCtx -> IO ()

-- | /ca_condense_field/ /res/ /ctx/ 
--
-- Attempts to demote the value of /res/ to a trivial subfield of its
-- current field by removing unused generators. In particular, this demotes
-- any obviously rational value to the trivial field \(\mathbb{Q}\).
-- 
-- This function is applied automatically in most operations (arithmetic
-- operations, etc.).
foreign import ccall "ca.h ca_condense_field"
  ca_condense_field :: Ptr CCa -> Ptr CCaCtx -> IO ()

-- | /ca_is_gen_as_ext/ /x/ /ctx/ 
--
-- If /x/ is a generator of its formal field,
-- \(x = a_k \in \mathbb{Q}(a_1,\ldots,a_n)\), returns a pointer to the
-- extension number defining \(a_k\). If /x/ is not a generator, returns
-- /NULL/.
foreign import ccall "ca.h ca_is_gen_as_ext"
  ca_is_gen_as_ext :: Ptr CCa -> Ptr CCaCtx -> IO (Ptr CCa)

-- Arithmetic ------------------------------------------------------------------

-- | /ca_neg/ /res/ /x/ /ctx/ 
--
-- Sets /res/ to the negation of /x/. For numbers, this operation amounts
-- to a direct negation within the formal field. For a signed infinity
-- \(c \infty\), negation gives \((-c) \infty\); all other special values
-- are unchanged.
foreign import ccall "ca.h ca_neg"
  ca_neg :: Ptr CCa -> Ptr CCa -> Ptr CCaCtx -> IO ()

-- | /ca_add_fmpq/ /res/ /x/ /y/ /ctx/ 
foreign import ccall "ca.h ca_add_fmpq"
  ca_add_fmpq :: Ptr CCa -> Ptr CCa -> Ptr CFmpq -> Ptr CCaCtx -> IO ()
  
-- | /ca_add_fmpz/ /res/ /x/ /y/ /ctx/ 
foreign import ccall "ca.h ca_add_fmpz"
  ca_add_fmpz :: Ptr CCa -> Ptr CCa -> Ptr CFmpz -> Ptr CCaCtx -> IO ()
  
-- | /ca_add_ui/ /res/ /x/ /y/ /ctx/ 
foreign import ccall "ca.h ca_add_ui"
  ca_add_ui :: Ptr CCa -> Ptr CCa -> CULong -> Ptr CCaCtx -> IO ()
  
-- | /ca_add_si/ /res/ /x/ /y/ /ctx/ 
foreign import ccall "ca.h ca_add_si"
  ca_add_si :: Ptr CCa -> Ptr CCa -> CLong -> Ptr CCaCtx -> IO ()
-- | /ca_add/ /res/ /x/ /y/ /ctx/ 
--
-- Sets /res/ to the sum of /x/ and /y/. For special values, the following
-- rules apply (c infty denotes a signed infinity, \(|c| = 1\)):
-- 
-- -   \(c \infty + d \infty = c \infty\) if \(c = d\)
-- -   \(c \infty + d \infty = \text{Undefined}\) if \(c \ne d\)
-- -   \(\tilde \infty + c \infty = \tilde \infty + \tilde \infty = \text{Undefined}\)
-- -   \(c \infty + z = c \infty\) if \(z \in \mathbb{C}\)
-- -   \(\tilde \infty + z = \tilde \infty\) if \(z \in \mathbb{C}\)
-- -   \(z + \text{Undefined} = \text{Undefined}\) for any value /z/
--     (including /Unknown/)
-- 
-- In any other case involving special values, or if the specific case
-- cannot be distinguished, the result is /Unknown/.
foreign import ccall "ca.h ca_add"
  ca_add :: Ptr CCa -> Ptr CCa -> Ptr CCa -> Ptr CCaCtx -> IO ()

-- | /ca_sub_fmpq/ /res/ /x/ /y/ /ctx/ 
foreign import ccall "ca.h ca_sub_fmpq"
  ca_sub_fmpq :: Ptr CCa -> Ptr CCa -> Ptr CFmpq -> Ptr CCaCtx -> IO ()
-- | /ca_sub_fmpz/ /res/ /x/ /y/ /ctx/ 
foreign import ccall "ca.h ca_sub_fmpz"
  ca_sub_fmpz :: Ptr CCa -> Ptr CCa -> Ptr CFmpz -> Ptr CCaCtx -> IO ()
-- | /ca_sub_ui/ /res/ /x/ /y/ /ctx/ 
foreign import ccall "ca.h ca_sub_ui"
  ca_sub_ui :: Ptr CCa -> Ptr CCa -> CULong -> Ptr CCaCtx -> IO ()
-- | /ca_sub_si/ /res/ /x/ /y/ /ctx/ 
foreign import ccall "ca.h ca_sub_si"
  ca_sub_si :: Ptr CCa -> Ptr CCa -> CLong -> Ptr CCaCtx -> IO ()
-- | /ca_fmpq_sub/ /res/ /x/ /y/ /ctx/ 
foreign import ccall "ca.h ca_fmpq_sub"
  ca_fmpq_sub :: Ptr CCa -> Ptr CFmpq -> Ptr CCa -> Ptr CCaCtx -> IO ()
-- | /ca_fmpz_sub/ /res/ /x/ /y/ /ctx/ 
foreign import ccall "ca.h ca_fmpz_sub"
  ca_fmpz_sub :: Ptr CCa -> Ptr CFmpz -> Ptr CCa -> Ptr CCaCtx -> IO ()
-- | /ca_ui_sub/ /res/ /x/ /y/ /ctx/ 
foreign import ccall "ca.h ca_ui_sub"
  ca_ui_sub :: Ptr CCa -> CULong -> Ptr CCa -> Ptr CCaCtx -> IO ()
-- | /ca_si_sub/ /res/ /x/ /y/ /ctx/ 
foreign import ccall "ca.h ca_si_sub"
  ca_si_sub :: Ptr CCa -> CLong -> Ptr CCa -> Ptr CCaCtx -> IO ()
-- | /ca_sub/ /res/ /x/ /y/ /ctx/ 
--
-- Sets /res/ to the difference of /x/ and /y/. This is equivalent to
-- computing \(x + (-y)\).
foreign import ccall "ca.h ca_sub"
  ca_sub :: Ptr CCa -> Ptr CCa -> Ptr CCa -> Ptr CCaCtx -> IO ()

-- | /ca_mul_fmpq/ /res/ /x/ /y/ /ctx/ 
foreign import ccall "ca.h ca_mul_fmpq"
  ca_mul_fmpq :: Ptr CCa -> Ptr CCa -> Ptr CFmpq -> Ptr CCaCtx -> IO ()
-- | /ca_mul_fmpz/ /res/ /x/ /y/ /ctx/ 
foreign import ccall "ca.h ca_mul_fmpz"
  ca_mul_fmpz :: Ptr CCa -> Ptr CCa -> Ptr CFmpz -> Ptr CCaCtx -> IO ()
-- | /ca_mul_ui/ /res/ /x/ /y/ /ctx/ 
foreign import ccall "ca.h ca_mul_ui"
  ca_mul_ui :: Ptr CCa -> Ptr CCa -> CULong -> Ptr CCaCtx -> IO ()
-- | /ca_mul_si/ /res/ /x/ /y/ /ctx/ 
foreign import ccall "ca.h ca_mul_si"
  ca_mul_si :: Ptr CCa -> Ptr CCa -> CLong -> Ptr CCaCtx -> IO ()
-- | /ca_mul/ /res/ /x/ /y/ /ctx/ 
--
-- Sets /res/ to the product of /x/ and /y/. For special values, the
-- following rules apply (c infty denotes a signed infinity, \(|c| = 1\)):
-- 
-- -   \(c \infty \cdot d \infty = c d \infty\)
-- -   \(c \infty \cdot \tilde \infty = \tilde \infty\)
-- -   \(\tilde \infty \cdot \tilde \infty = \tilde \infty\)
-- -   \(c \infty \cdot z = \operatorname{sgn}(z) c \infty\) if
--     \(z \in \mathbb{C} \setminus \{0\}\)
-- -   \(c \infty \cdot 0 = \text{Undefined}\)
-- -   \(\tilde \infty \cdot 0 = \text{Undefined}\)
-- -   \(z \cdot  \text{Undefined} = \text{Undefined}\) for any value /z/
--     (including /Unknown/)
-- 
-- In any other case involving special values, or if the specific case
-- cannot be distinguished, the result is /Unknown/.
foreign import ccall "ca.h ca_mul"
  ca_mul :: Ptr CCa -> Ptr CCa -> Ptr CCa -> Ptr CCaCtx -> IO ()

-- | /ca_inv/ /res/ /x/ /ctx/ 
--
-- Sets /res/ to the multiplicative inverse of /x/. In a univariate
-- algebraic number field, this always produces a rational denominator, but
-- the denominator might not be rationalized in a multivariate field. For
-- special values and zero, the following rules apply:
-- 
-- -   \(1 / (c \infty) = 1 / \tilde \infty = 0\)
-- -   \(1 / 0 = \tilde \infty\)
-- -   \(1 / \text{Undefined} = \text{Undefined}\)
-- -   \(1 / \text{Unknown} = \text{Unknown}\)
-- 
-- If it cannot be determined whether /x/ is zero or nonzero, the result is
-- /Unknown/.
foreign import ccall "ca.h ca_inv"
  ca_inv :: Ptr CCa -> Ptr CCa -> Ptr CCaCtx -> IO ()

-- | /ca_fmpq_div/ /res/ /x/ /y/ /ctx/ 
foreign import ccall "ca.h ca_fmpq_div"
  ca_fmpq_div :: Ptr CCa -> Ptr CFmpq -> Ptr CCa -> Ptr CCaCtx -> IO ()
-- | /ca_fmpz_div/ /res/ /x/ /y/ /ctx/ 
foreign import ccall "ca.h ca_fmpz_div"
  ca_fmpz_div :: Ptr CCa -> Ptr CFmpz -> Ptr CCa -> Ptr CCaCtx -> IO ()
-- | /ca_ui_div/ /res/ /x/ /y/ /ctx/ 
foreign import ccall "ca.h ca_ui_div"
  ca_ui_div :: Ptr CCa -> CULong -> Ptr CCa -> Ptr CCaCtx -> IO ()
-- | /ca_si_div/ /res/ /x/ /y/ /ctx/ 
foreign import ccall "ca.h ca_si_div"
  ca_si_div :: Ptr CCa -> CLong -> Ptr CCa -> Ptr CCaCtx -> IO ()
-- | /ca_div_fmpq/ /res/ /x/ /y/ /ctx/ 
foreign import ccall "ca.h ca_div_fmpq"
  ca_div_fmpq :: Ptr CCa -> Ptr CCa -> Ptr CFmpq -> Ptr CCaCtx -> IO ()
-- | /ca_div_fmpz/ /res/ /x/ /y/ /ctx/ 
foreign import ccall "ca.h ca_div_fmpz"
  ca_div_fmpz :: Ptr CCa -> Ptr CCa -> Ptr CFmpz -> Ptr CCaCtx -> IO ()
-- | /ca_div_ui/ /res/ /x/ /y/ /ctx/ 
foreign import ccall "ca.h ca_div_ui"
  ca_div_ui :: Ptr CCa -> Ptr CCa -> CULong -> Ptr CCaCtx -> IO ()
-- | /ca_div_si/ /res/ /x/ /y/ /ctx/ 
foreign import ccall "ca.h ca_div_si"
  ca_div_si :: Ptr CCa -> Ptr CCa -> CLong -> Ptr CCaCtx -> IO ()
-- | /ca_div/ /res/ /x/ /y/ /ctx/ 
--
-- Sets /res/ to the quotient of /x/ and /y/. This is equivalent to
-- computing \(x \cdot (1 / y)\). For special values and division by zero,
-- this implies the following rules (c infty denotes a signed infinity,
-- \(|c| = 1\)):
-- 
-- -   \((c \infty) / (d \infty) = (c \infty) / \tilde \infty = \tilde \infty / (c \infty) = \tilde \infty / \tilde \infty = \text{Undefined}\)
-- -   \(c \infty / z = (c / \operatorname{sgn}(z)) \infty\) if
--     \(z \in \mathbb{C} \setminus \{0\}\)
-- -   \(c \infty / 0 = \tilde \infty / 0 = \tilde \infty\)
-- -   \(z / (c \infty) = z / \tilde \infty = 0\) if \(z \in \mathbb{C}\)
-- -   \(z / 0 = \tilde \infty\) if \(z \in \mathbb{C} \setminus \{0\}\)
-- -   \(0 / 0 = \text{Undefined}\)
-- -   \(z / \text{Undefined} = \text{Undefined}\) for any value /z/
--     (including /Unknown/)
-- -   \(\text{Undefined} / z = \text{Undefined}\) for any value /z/
--     (including /Unknown/)
-- 
-- In any other case involving special values, or if the specific case
-- cannot be distinguished, the result is /Unknown/.
foreign import ccall "ca.h ca_div"
  ca_div :: Ptr CCa -> Ptr CCa -> Ptr CCa -> Ptr CCaCtx -> IO ()

-- | /ca_dot/ /res/ /initial/ /subtract/ /x/ /xstep/ /y/ /ystep/ /len/ /ctx/ 
--
-- Computes the dot product of the vectors /x/ and /y/, setting /res/ to
-- \(s + (-1)^{subtract} \sum_{i=0}^{len-1} x_i y_i\).
-- 
-- The initial term /s/ is optional and can be omitted by passing /NULL/
-- (equivalently, \(s = 0\)). The parameter /subtract/ must be 0 or 1. The
-- length /len/ is allowed to be negative, which is equivalent to a length
-- of zero. The parameters /xstep/ or /ystep/ specify a step length for
-- traversing subsequences of the vectors /x/ and /y/; either can be
-- negative to step in the reverse direction starting from the initial
-- pointer. Aliasing is allowed between /res/ and /s/ but not between /res/
-- and the entries of /x/ and /y/.
foreign import ccall "ca.h ca_dot"
  ca_dot :: Ptr CCa -> Ptr CCa -> CInt -> Ptr CCa -> CLong -> Ptr CCa -> CLong -> CLong -> Ptr CCaCtx -> IO ()

-- | /ca_fmpz_poly_evaluate/ /res/ /poly/ /x/ /ctx/ 
foreign import ccall "ca.h ca_fmpz_poly_evaluate"
  ca_fmpz_poly_evaluate :: Ptr CCa -> Ptr CFmpzPoly -> Ptr CCa -> Ptr CCaCtx -> IO ()
-- | /ca_fmpq_poly_evaluate/ /res/ /poly/ /x/ /ctx/ 
--
-- Sets /res/ to the polynomial /poly/ evaluated at /x/.
foreign import ccall "ca.h ca_fmpq_poly_evaluate"
  ca_fmpq_poly_evaluate :: Ptr CCa -> Ptr CFmpqPoly -> Ptr CCa -> Ptr CCaCtx -> IO ()

-- | /ca_fmpz_mpoly_evaluate_horner/ /res/ /f/ /x/ /mctx/ /ctx/ 
foreign import ccall "ca.h ca_fmpz_mpoly_evaluate_horner"
  ca_fmpz_mpoly_evaluate_horner :: Ptr CCa -> Ptr CFmpzMPoly -> Ptr CCa -> Ptr CFmpzMPolyCtx -> Ptr CCaCtx -> IO ()
-- -- | /ca_fmpz_mpoly_evaluate_iter/ /res/ /f/ /x/ /mctx/ /ctx/ 
-- foreign import ccall "ca.h ca_fmpz_mpoly_evaluate_iter"
--   ca_fmpz_mpoly_evaluate_iter :: Ptr CCa -> Ptr CFmpzMPoly -> Ptr CCa -> Ptr CFmpzMPolyCtx -> Ptr CCaCtx -> IO ()
-- | /ca_fmpz_mpoly_evaluate/ /res/ /f/ /x/ /mctx/ /ctx/ 
--
-- Sets /res/ to the multivariate polynomial /f/ evaluated at the vector of
-- arguments /x/.
foreign import ccall "ca.h ca_fmpz_mpoly_evaluate"
  ca_fmpz_mpoly_evaluate :: Ptr CCa -> Ptr CFmpzMPoly -> Ptr CCa -> Ptr CFmpzMPolyCtx -> Ptr CCaCtx -> IO ()

-- | /ca_fmpz_mpoly_q_evaluate/ /res/ /f/ /x/ /mctx/ /ctx/ 
--
-- Sets /res/ to the multivariate rational function /f/ evaluated at the
-- vector of arguments /x/.
foreign import ccall "ca.h ca_fmpz_mpoly_q_evaluate"
  ca_fmpz_mpoly_q_evaluate :: Ptr CCa -> Ptr CFmpzMPolyQ -> Ptr CCa -> Ptr CFmpzMPolyCtx -> Ptr CCaCtx -> IO ()

-- | /ca_fmpz_mpoly_q_evaluate_no_division_by_zero/ /res/ /f/ /x/ /mctx/ /ctx/ 
foreign import ccall "ca.h ca_fmpz_mpoly_q_evaluate_no_division_by_zero"
  ca_fmpz_mpoly_q_evaluate_no_division_by_zero :: Ptr CCa -> Ptr CFmpzMPolyQ -> Ptr CCa -> Ptr CFmpzMPolyCtx -> Ptr CCaCtx -> IO ()
-- | /ca_inv_no_division_by_zero/ /res/ /x/ /ctx/ 
--
-- These functions behave like the normal arithmetic functions, but assume
-- (and do not check) that division by zero cannot occur. Division by zero
-- will result in undefined behavior.
foreign import ccall "ca.h ca_inv_no_division_by_zero"
  ca_inv_no_division_by_zero :: Ptr CCa -> Ptr CCa -> Ptr CCaCtx -> IO ()

-- Powers and roots ------------------------------------------------------------

-- | /ca_sqr/ /res/ /x/ /ctx/ 
--
-- Sets /res/ to the square of /x/.
foreign import ccall "ca.h ca_sqr"
  ca_sqr :: Ptr CCa -> Ptr CCa -> Ptr CCaCtx -> IO ()

-- | /ca_pow_fmpq/ /res/ /x/ /y/ /ctx/ 
foreign import ccall "ca.h ca_pow_fmpq"
  ca_pow_fmpq :: Ptr CCa -> Ptr CCa -> Ptr CFmpq -> Ptr CCaCtx -> IO ()
-- | /ca_pow_fmpz/ /res/ /x/ /y/ /ctx/ 
foreign import ccall "ca.h ca_pow_fmpz"
  ca_pow_fmpz :: Ptr CCa -> Ptr CCa -> Ptr CFmpz -> Ptr CCaCtx -> IO ()
-- | /ca_pow_ui/ /res/ /x/ /y/ /ctx/ 
foreign import ccall "ca.h ca_pow_ui"
  ca_pow_ui :: Ptr CCa -> Ptr CCa -> CULong -> Ptr CCaCtx -> IO ()
-- | /ca_pow_si/ /res/ /x/ /y/ /ctx/ 
foreign import ccall "ca.h ca_pow_si"
  ca_pow_si :: Ptr CCa -> Ptr CCa -> CLong -> Ptr CCaCtx -> IO ()
-- | /ca_pow/ /res/ /x/ /y/ /ctx/ 
--
-- Sets /res/ to /x/ raised to the power /y/. Handling of special values is
-- not yet implemented.
foreign import ccall "ca.h ca_pow"
  ca_pow :: Ptr CCa -> Ptr CCa -> Ptr CCa -> Ptr CCaCtx -> IO ()

-- | /ca_pow_si_arithmetic/ /res/ /x/ /n/ /ctx/ 
--
-- Sets /res/ to /x/ raised to the power /n/. Whereas @ca_pow@, @ca_pow_si@
-- etc. may create \(x^n\) as an extension number if /n/ is large, this
-- function always perform the exponentiation using field arithmetic.
foreign import ccall "ca.h ca_pow_si_arithmetic"
  ca_pow_si_arithmetic :: Ptr CCa -> Ptr CCa -> CLong -> Ptr CCaCtx -> IO ()

-- | /ca_sqrt_inert/ /res/ /x/ /ctx/ 
foreign import ccall "ca.h ca_sqrt_inert"
  ca_sqrt_inert :: Ptr CCa -> Ptr CCa -> Ptr CCaCtx -> IO ()
-- | /ca_sqrt_nofactor/ /res/ /x/ /ctx/ 
foreign import ccall "ca.h ca_sqrt_nofactor"
  ca_sqrt_nofactor :: Ptr CCa -> Ptr CCa -> Ptr CCaCtx -> IO ()
-- | /ca_sqrt_factor/ /res/ /x/ /flags/ /ctx/ 
foreign import ccall "ca.h ca_sqrt_factor"
  ca_sqrt_factor :: Ptr CCa -> Ptr CCa -> CULong -> Ptr CCaCtx -> IO ()
-- | /ca_sqrt/ /res/ /x/ /ctx/ 
--
-- Sets /res/ to the principal square root of /x/.
-- 
-- For special values, the following definitions apply:
-- 
-- -   \(\sqrt{c \infty} = \sqrt{c} \infty\)
-- -   \(\sqrt{\tilde \infty} = \tilde \infty\).
-- -   Both /Undefined/ and /Unknown/ map to themselves.
-- 
-- The /inert/ version outputs the generator in the formal field
-- \(\mathbb{Q}(\sqrt{x})\) without simplifying.
-- 
-- The /factor/ version writes \(x = A^2 B\) in \(K\) where \(K\) is the
-- field of /x/, and outputs \(A \sqrt{B}\) or \(-A \sqrt{B}\) (whichever
-- gives the correct sign) as an element of \(K(\sqrt{B})\) or some
-- subfield thereof. This factorization is only a heuristic and is not
-- guaranteed to make \(B\) minimal. Factorization options can be passed
-- through to /flags/: see @ca_factor@ for details.
-- 
-- The /nofactor/ version will not perform a general factorization, but may
-- still perform other simplifications. It may in particular attempt to
-- simplify \(\sqrt{x}\) to a single element in \(\overline{\mathbb{Q}}\).
foreign import ccall "ca.h ca_sqrt"
  ca_sqrt :: Ptr CCa -> Ptr CCa -> Ptr CCaCtx -> IO ()

-- | /ca_sqrt_ui/ /res/ /n/ /ctx/ 
--
-- Sets /res/ to the principal square root of /n/.
foreign import ccall "ca.h ca_sqrt_ui"
  ca_sqrt_ui :: Ptr CCa -> CULong -> Ptr CCaCtx -> IO ()

-- Complex parts ---------------------------------------------------------------

-- | /ca_abs/ /res/ /x/ /ctx/ 
--
-- Sets /res/ to the absolute value of /x/.
-- 
-- For special values, the following definitions apply:
-- 
-- -   \(|c \infty| = |\tilde \infty| = +\infty\).
-- -   Both /Undefined/ and /Unknown/ map to themselves.
-- 
-- This function will attempt to simplify its argument through an exact
-- computation. It may in particular attempt to simplify \(|x|\) to a
-- single element in \(\overline{\mathbb{Q}}\).
-- 
-- In the generic case, this function outputs an element of the formal
-- field \(\mathbb{Q}(|x|)\).
foreign import ccall "ca.h ca_abs"
  ca_abs :: Ptr CCa -> Ptr CCa -> Ptr CCaCtx -> IO ()

-- | /ca_sgn/ /res/ /x/ /ctx/ 
--
-- Sets /res/ to the sign of /x/, defined by
-- 
-- \[`\]
-- \[\begin{aligned}
-- \operatorname{sgn}(x) = \begin{cases} 0 & x = 0 \\ \frac{x}{|x|} & x \ne 0 \end{cases}
-- \end{aligned}\]
-- 
-- for numbers. For special values, the following definitions apply:
-- 
-- -   \(\operatorname{sgn}(c \infty) = c\).
-- -   \(\operatorname{sgn}(\tilde \infty) = \operatorname{Undefined}\).
-- -   Both /Undefined/ and /Unknown/ map to themselves.
-- 
-- This function will attempt to simplify its argument through an exact
-- computation. It may in particular attempt to simplify
-- \(\operatorname{sgn}(x)\) to a single element in
-- \(\overline{\mathbb{Q}}\).
-- 
-- In the generic case, this function outputs an element of the formal
-- field \(\mathbb{Q}(\operatorname{sgn}(x))\).
foreign import ccall "ca.h ca_sgn"
  ca_sgn :: Ptr CCa -> Ptr CCa -> Ptr CCaCtx -> IO ()

-- | /ca_csgn/ /res/ /x/ /ctx/ 
--
-- Sets /res/ to the extension of the real sign function taking the value 1
-- for /z/ strictly in the right half plane, -1 for /z/ strictly in the
-- left half plane, and the sign of the imaginary part when /z/ is on the
-- imaginary axis. Equivalently,
-- \(\operatorname{csgn}(z) = z / \sqrt{z^2}\) except that the value is 0
-- when /z/ is exactly zero. This function gives /Undefined/ for unsigned
-- infinity and
-- \(\operatorname{csgn}(\operatorname{sgn}(c \infty)) = \operatorname{csgn}(c)\)
-- for signed infinities.
foreign import ccall "ca.h ca_csgn"
  ca_csgn :: Ptr CCa -> Ptr CCa -> Ptr CCaCtx -> IO ()

-- | /ca_arg/ /res/ /x/ /ctx/ 
--
-- Sets /res/ to the complex argument (phase) of /x/, normalized to the
-- range \((-\pi, +\pi]\). The argument of 0 is defined as 0. For special
-- values, the following definitions apply:
-- 
-- -   \(\operatorname{arg}(c \infty) = \operatorname{arg}(c)\).
-- -   \(\operatorname{arg}(\tilde \infty) = \operatorname{Undefined}\).
-- -   Both /Undefined/ and /Unknown/ map to themselves.
foreign import ccall "ca.h ca_arg"
  ca_arg :: Ptr CCa -> Ptr CCa -> Ptr CCaCtx -> IO ()

-- | /ca_re/ /res/ /x/ /ctx/ 
--
-- Sets /res/ to the real part of /x/. The result is /Undefined/ if /x/ is
-- any infinity (including a real infinity).
foreign import ccall "ca.h ca_re"
  ca_re :: Ptr CCa -> Ptr CCa -> Ptr CCaCtx -> IO ()

-- | /ca_im/ /res/ /x/ /ctx/ 
--
-- Sets /res/ to the imaginary part of /x/. The result is /Undefined/ if
-- /x/ is any infinity (including an imaginary infinity).
foreign import ccall "ca.h ca_im"
  ca_im :: Ptr CCa -> Ptr CCa -> Ptr CCaCtx -> IO ()

-- | /ca_conj_deep/ /res/ /x/ /ctx/ 
foreign import ccall "ca.h ca_conj_deep"
  ca_conj_deep :: Ptr CCa -> Ptr CCa -> Ptr CCaCtx -> IO ()
-- | /ca_conj_shallow/ /res/ /x/ /ctx/ 
foreign import ccall "ca.h ca_conj_shallow"
  ca_conj_shallow :: Ptr CCa -> Ptr CCa -> Ptr CCaCtx -> IO ()
-- | /ca_conj/ /res/ /x/ /ctx/ 
--
-- Sets /res/ to the complex conjugate of /x/. The /shallow/ version
-- creates a new extension element \(\overline{x}\) unless /x/ can be
-- trivially conjugated in-place in the existing field. The /deep/ version
-- recursively conjugates the extension numbers in the field of /x/.
foreign import ccall "ca.h ca_conj"
  ca_conj :: Ptr CCa -> Ptr CCa -> Ptr CCaCtx -> IO ()

-- | /ca_floor/ /res/ /x/ /ctx/ 
--
-- Sets /res/ to the floor function of /x/. The result is /Undefined/ if
-- /x/ is any infinity (including a real infinity). For complex numbers,
-- this is presently defined to take the floor of the real part.
foreign import ccall "ca.h ca_floor"
  ca_floor :: Ptr CCa -> Ptr CCa -> Ptr CCaCtx -> IO ()

-- | /ca_ceil/ /res/ /x/ /ctx/ 
--
-- Sets /res/ to the ceiling function of /x/. The result is /Undefined/ if
-- /x/ is any infinity (including a real infinity). For complex numbers,
-- this is presently defined to take the ceiling of the real part.
foreign import ccall "ca.h ca_ceil"
  ca_ceil :: Ptr CCa -> Ptr CCa -> Ptr CCaCtx -> IO ()

-- Exponentials and logarithms -------------------------------------------------

-- | /ca_exp/ /res/ /x/ /ctx/ 
--
-- Sets /res/ to the exponential function of /x/.
-- 
-- For special values, the following definitions apply:
-- 
-- -   \(e^{+\infty} = +\infty\)
-- -   \(e^{c \infty} = \tilde \infty\) if
--     \(0 < \operatorname{Re}(c) < 1\).
-- -   \(e^{c \infty} = 0\) if \(\operatorname{Re}(c) < 0\).
-- -   \(e^{c \infty} = \text{Undefined}\) if \(\operatorname{Re}(c) = 0\).
-- -   \(e^{\tilde \infty} = \text{Undefined}\).
-- -   Both /Undefined/ and /Unknown/ map to themselves.
-- 
-- The following symbolic simplifications are performed automatically:
-- 
-- -   \(e^0 = 1\)
-- -   \(e^{\log(z)} = z\)
-- -   \(e^{(p/q) \log(z)} = z^{p/q}\) (for rational \(p/q\))
-- -   \(e^{(p/q) \pi i}\) = algebraic root of unity (for small rational
--     \(p/q\))
-- 
-- In the generic case, this function outputs an element of the formal
-- field \(\mathbb{Q}(e^x)\).
foreign import ccall "ca.h ca_exp"
  ca_exp :: Ptr CCa -> Ptr CCa -> Ptr CCaCtx -> IO ()

-- | /ca_log/ /res/ /x/ /ctx/ 
--
-- Sets /res/ to the natural logarithm of /x/.
-- 
-- For special values and at the origin, the following definitions apply:
-- 
-- -   For any infinity, \(\log(c\infty) = \log(\tilde \infty) = +\infty\).
-- -   \(\log(0) = -\infty\). The result is /Unknown/ if deciding \(x = 0\)
--     fails.
-- -   Both /Undefined/ and /Unknown/ map to themselves.
-- 
-- The following symbolic simplifications are performed automatically:
-- 
-- -   \(\log(1) = 0\)
-- -   \(\log\left(e^z\right) = z + 2 \pi i k\)
-- -   \(\log\left(\sqrt{z}\right) = \tfrac{1}{2} \log(z) + 2 \pi i k\)
-- -   \(\log\left(z^a\right) = a \log(z) + 2 \pi i k\)
-- -   \(\log(x) = \log(-x) + \pi i\) for negative real /x/
-- 
-- In the generic case, this function outputs an element of the formal
-- field \(\mathbb{Q}(\log(x))\).
foreign import ccall "ca.h ca_log"
  ca_log :: Ptr CCa -> Ptr CCa -> Ptr CCaCtx -> IO ()

-- Trigonometric functions -----------------------------------------------------

-- | /ca_sin_cos_exponential/ /res1/ /res2/ /x/ /ctx/ 
foreign import ccall "ca.h ca_sin_cos_exponential"
  ca_sin_cos_exponential :: Ptr CCa -> Ptr CCa -> Ptr CCa -> Ptr CCaCtx -> IO ()
-- | /ca_sin_cos_direct/ /res1/ /res2/ /x/ /ctx/ 
foreign import ccall "ca.h ca_sin_cos_direct"
  ca_sin_cos_direct :: Ptr CCa -> Ptr CCa -> Ptr CCa -> Ptr CCaCtx -> IO ()
-- | /ca_sin_cos_tangent/ /res1/ /res2/ /x/ /ctx/ 
foreign import ccall "ca.h ca_sin_cos_tangent"
  ca_sin_cos_tangent :: Ptr CCa -> Ptr CCa -> Ptr CCa -> Ptr CCaCtx -> IO ()
-- | /ca_sin_cos/ /res1/ /res2/ /x/ /ctx/ 
--
-- Sets /res1/ to the sine of /x/ and /res2/ to the cosine of /x/. Either
-- /res1/ or /res2/ can be /NULL/ to compute only the other function.
-- Various representations are implemented:
-- 
-- -   The /exponential/ version expresses the sine and cosine in terms of
--     complex exponentials. Simple algebraic values will simplify to
--     rational numbers or elements of cyclotomic fields.
-- -   The /direct/ method expresses the sine and cosine in terms of the
--     original functions (perhaps after applying some symmetry
--     transformations, which may interchange sin and cos). Extremely
--     simple algebraic values will automatically simplify to elements of
--     real algebraic number fields.
-- -   The /tangent/ version expresses the sine and cosine in terms of
--     \(\tan(x/2)\), perhaps after applying some symmetry transformations.
--     Extremely simple algebraic values will automatically simplify to
--     elements of real algebraic number fields.
-- 
-- By default, the standard function uses the /exponential/ representation
-- as this typically works best for field arithmetic and simplifications,
-- although it has the disadvantage of introducing complex numbers where
-- real numbers would be sufficient. The behavior of the standard function
-- can be changed using the @ca_opt_trigformM@ context setting.
-- 
-- For special values, the following definitions apply:
-- 
-- -   \(\sin(\pm i \infty) = \pm i \infty\)
-- -   \(\cos(\pm i \infty) = +\infty\)
-- -   All other infinities give \(\operatorname{Undefined}\)
foreign import ccall "ca.h ca_sin_cos"
  ca_sin_cos :: Ptr CCa -> Ptr CCa -> Ptr CCa -> Ptr CCaCtx -> IO ()

-- | /ca_sin/ /res/ /x/ /ctx/ 
foreign import ccall "ca.h ca_sin"
  ca_sin :: Ptr CCa -> Ptr CCa -> Ptr CCaCtx -> IO ()
-- | /ca_cos/ /res/ /x/ /ctx/ 
--
-- Sets /res/ to the sine or cosine of /x/. These functions are shortcuts
-- for @ca_sin_cos@.
foreign import ccall "ca.h ca_cos"
  ca_cos :: Ptr CCa -> Ptr CCa -> Ptr CCaCtx -> IO ()

-- | /ca_tan_sine_cosine/ /res/ /x/ /ctx/ 
foreign import ccall "ca.h ca_tan_sine_cosine"
  ca_tan_sine_cosine :: Ptr CCa -> Ptr CCa -> Ptr CCaCtx -> IO ()
-- | /ca_tan_exponential/ /res/ /x/ /ctx/ 
foreign import ccall "ca.h ca_tan_exponential"
  ca_tan_exponential :: Ptr CCa -> Ptr CCa -> Ptr CCaCtx -> IO ()
-- | /ca_tan_direct/ /res/ /x/ /ctx/ 
foreign import ccall "ca.h ca_tan_direct"
  ca_tan_direct :: Ptr CCa -> Ptr CCa -> Ptr CCaCtx -> IO ()
-- | /ca_tan/ /res/ /x/ /ctx/ 
--
-- Sets /res/ to the tangent of /x/. The /sine_cosine/ version evaluates
-- the tangent as a quotient of a sine and cosine, the /direct/ version
-- evaluates it directly as a tangent (possibly after transforming the
-- variable), and the /exponential/ version evaluates it in terms of
-- complex exponentials. Simple algebraic values will automatically
-- simplify to elements of trigonometric or cyclotomic number fields.
-- 
-- By default, the standard function uses the /exponential/ representation
-- as this typically works best for field arithmetic and simplifications,
-- although it has the disadvantage of introducing complex numbers where
-- real numbers would be sufficient. The behavior of the standard function
-- can be changed using the @CA_OPT_TRIG_FORM@ context setting.
-- 
-- For special values, the following definitions apply:
-- 
-- -   At poles, \(\tan((n+\tfrac{1}{2}) \pi) = \tilde \infty\)
-- -   \(\tan(e^{i \theta} \infty) = +i, \quad 0 < \theta < \pi\)
-- -   \(\tan(e^{i \theta} \infty) = -i, \quad -\pi < \theta < 0\)
-- -   \(\tan(\pm \infty) = \tan(\tilde \infty) = \operatorname{Undefined}\)
foreign import ccall "ca.h ca_tan"
  ca_tan :: Ptr CCa -> Ptr CCa -> Ptr CCaCtx -> IO ()

-- | /ca_cot/ /res/ /x/ /ctx/ 
--
-- Sets /res/ to the cotangent /x/. This is equivalent to computing the
-- reciprocal of the tangent.
foreign import ccall "ca.h ca_cot"
  ca_cot :: Ptr CCa -> Ptr CCa -> Ptr CCaCtx -> IO ()

-- | /ca_atan_logarithm/ /res/ /x/ /ctx/ 
foreign import ccall "ca.h ca_atan_logarithm"
  ca_atan_logarithm :: Ptr CCa -> Ptr CCa -> Ptr CCaCtx -> IO ()
-- | /ca_atan_direct/ /res/ /x/ /ctx/ 
foreign import ccall "ca.h ca_atan_direct"
  ca_atan_direct :: Ptr CCa -> Ptr CCa -> Ptr CCaCtx -> IO ()
-- | /ca_atan/ /res/ /x/ /ctx/ 
--
-- Sets /res/ to the inverse tangent of /x/.
-- 
-- The /direct/ version expresses the result as an inverse tangent
-- (possibly after transforming the variable). The /logarithm/ version
-- expresses it in terms of complex logarithms. Simple algebraic inputs
-- will automatically simplify to rational multiples of \(\pi\).
-- 
-- By default, the standard function uses the /logarithm/ representation as
-- this typically works best for field arithmetic and simplifications,
-- although it has the disadvantage of introducing complex numbers where
-- real numbers would be sufficient. The behavior of the standard function
-- can be changed using the @CA_OPT_TRIG_FORM@ context setting (exponential
-- mode results in logarithmic forms).
-- 
-- For special values, the following definitions apply:
-- 
-- -   \(\operatorname{atan}(\pm i) = \pm i \infty\)
-- -   \(\operatorname{atan}(c \infty) = \operatorname{csgn}(c) \pi / 2\)
-- -   \(\operatorname{atan}(\tilde \infty) = \operatorname{Undefined}\)
foreign import ccall "ca.h ca_atan"
  ca_atan :: Ptr CCa -> Ptr CCa -> Ptr CCaCtx -> IO ()

-- | /ca_asin_logarithm/ /res/ /x/ /ctx/ 
foreign import ccall "ca.h ca_asin_logarithm"
  ca_asin_logarithm :: Ptr CCa -> Ptr CCa -> Ptr CCaCtx -> IO ()
-- | /ca_acos_logarithm/ /res/ /x/ /ctx/ 
foreign import ccall "ca.h ca_acos_logarithm"
  ca_acos_logarithm :: Ptr CCa -> Ptr CCa -> Ptr CCaCtx -> IO ()
-- | /ca_asin_direct/ /res/ /x/ /ctx/ 
foreign import ccall "ca.h ca_asin_direct"
  ca_asin_direct :: Ptr CCa -> Ptr CCa -> Ptr CCaCtx -> IO ()
-- | /ca_acos_direct/ /res/ /x/ /ctx/ 
foreign import ccall "ca.h ca_acos_direct"
  ca_acos_direct :: Ptr CCa -> Ptr CCa -> Ptr CCaCtx -> IO ()
-- | /ca_asin/ /res/ /x/ /ctx/ 
foreign import ccall "ca.h ca_asin"
  ca_asin :: Ptr CCa -> Ptr CCa -> Ptr CCaCtx -> IO ()
-- | /ca_acos/ /res/ /x/ /ctx/ 
--
-- Sets /res/ to the inverse sine (respectively, cosine) of /x/.
-- 
-- The /direct/ version expresses the result as an inverse sine or cosine
-- (possibly after transforming the variable). The /logarithm/ version
-- expresses it in terms of complex logarithms. Simple algebraic inputs
-- will automatically simplify to rational multiples of \(\pi\).
-- 
-- By default, the standard function uses the /logarithm/ representation as
-- this typically works best for field arithmetic and simplifications,
-- although it has the disadvantage of introducing complex numbers where
-- real numbers would be sufficient. The behavior of the standard function
-- can be changed using the @CA_OPT_TRIG_FORM@ context setting (exponential
-- mode results in logarithmic forms).
-- 
-- The inverse cosine is presently implemented as
-- \(\operatorname{acos}(x) = \pi/2 - \operatorname{asin}(x)\).
foreign import ccall "ca.h ca_acos"
  ca_acos :: Ptr CCa -> Ptr CCa -> Ptr CCaCtx -> IO ()

-- Special functions -----------------------------------------------------------

-- | /ca_gamma/ /res/ /x/ /ctx/ 
--
-- Sets /res/ to the gamma function of /x/.
foreign import ccall "ca.h ca_gamma"
  ca_gamma :: Ptr CCa -> Ptr CCa -> Ptr CCaCtx -> IO ()

-- | /ca_erf/ /res/ /x/ /ctx/ 
--
-- Sets /res/ to the error function of /x/.
foreign import ccall "ca.h ca_erf"
  ca_erf :: Ptr CCa -> Ptr CCa -> Ptr CCaCtx -> IO ()

-- | /ca_erfc/ /res/ /x/ /ctx/ 
--
-- Sets /res/ to the complementary error function of /x/.
foreign import ccall "ca.h ca_erfc"
  ca_erfc :: Ptr CCa -> Ptr CCa -> Ptr CCaCtx -> IO ()

-- | /ca_erfi/ /res/ /x/ /ctx/ 
--
-- Sets /res/ to the imaginary error function of /x/.
foreign import ccall "ca.h ca_erfi"
  ca_erfi :: Ptr CCa -> Ptr CCa -> Ptr CCaCtx -> IO ()

-- Numerical evaluation --------------------------------------------------------

-- | /ca_get_acb_raw/ /res/ /x/ /prec/ /ctx/ 
--
-- Sets /res/ to an enclosure of the numerical value of /x/. A working
-- precision of /prec/ bits is used internally for the evaluation, without
-- adaptive refinement. If /x/ is any special value, /res/ is set to
-- /acb_indeterminate/.
foreign import ccall "ca.h ca_get_acb_raw"
  ca_get_acb_raw :: Ptr CAcb -> Ptr CCa -> CLong -> Ptr CCaCtx -> IO ()

-- | /ca_get_acb/ /res/ /x/ /prec/ /ctx/ 
foreign import ccall "ca.h ca_get_acb"
  ca_get_acb :: Ptr CAcb -> Ptr CCa -> CLong -> Ptr CCaCtx -> IO ()
  
-- | /ca_get_acb_accurate_parts/ /res/ /x/ /prec/ /ctx/ 
--
-- Sets /res/ to an enclosure of the numerical value of /x/. The working
-- precision is increased adaptively to try to ensure /prec/ accurate bits
-- in the output. The /accurate_parts/ version tries to ensure /prec/
-- accurate bits for both the real and imaginary part separately.
-- 
-- The refinement is stopped if the working precision exceeds
-- @CA_OPT_PREC_LIMIT@ (or twice the initial precision, if this is larger).
-- The user may call /acb_rel_accuracy_bits/ to check is the calculation
-- was successful.
-- 
-- The output is not rounded down to /prec/ bits (to avoid unnecessary
-- double rounding); the user may call /acb_set_round/ when rounding is
-- desired.
foreign import ccall "ca.h ca_get_acb_accurate_parts"
  ca_get_acb_accurate_parts :: Ptr CAcb -> Ptr CCa -> CLong -> Ptr CCaCtx -> IO ()

-- | /ca_get_decimal_str/ /x/ /digits/ /flags/ /ctx/ 
--
-- Returns a decimal approximation of /x/ with precision up to /digits/.
-- The output is guaranteed to be correct within 1 ulp in the returned
-- digits, but the number of returned digits may be smaller than /digits/
-- if the numerical evaluation does not succeed.
-- 
-- If /flags/ is set to 1, attempts to achieve full accuracy for both the
-- real and imaginary parts separately.
-- 
-- If /x/ is not finite or a finite enclosure cannot be produced, returns
-- the string \"?\".
-- 
-- The user should free the returned string with @flint_free@.
foreign import ccall "ca.h ca_get_decimal_str"
  ca_get_decimal_str :: Ptr CCa -> CLong -> CULong -> Ptr CCaCtx -> IO CString

-- Rewriting and simplification ------------------------------------------------

-- | /ca_rewrite_complex_normal_form/ /res/ /x/ /deep/ /ctx/ 
--
-- Sets /res/ to /x/ rewritten using standardizing transformations over the
-- complex numbers:
-- 
-- -   Elementary functions are rewritten in terms of (complex)
--     exponentials, roots and logarithms
-- -   Complex parts are rewritten using logarithms, square roots, and
--     (deep) complex conjugates
-- -   Algebraic numbers are rewritten in terms of cyclotomic fields where
--     applicable
-- 
-- If /deep/ is set, the rewriting is applied recursively to the tower of
-- extension numbers; otherwise, the rewriting is only applied to the
-- top-level extension numbers.
-- 
-- The result is not a normal form in the strong sense (the same number can
-- have many possible representations even after applying this
-- transformation), but in practice this is a powerful heuristic for
-- simplification.
foreign import ccall "ca.h ca_rewrite_complex_normal_form"
  ca_rewrite_complex_normal_form :: Ptr CCa -> Ptr CCa -> CInt -> Ptr CCaCtx -> IO ()

-- Factorization ---------------------------------------------------------------

-- | /ca_factor_init/ /fac/ /ctx/ 
--
-- Initializes /fac/ and sets it to the empty factorization (equivalent to
-- the number 1).
foreign import ccall "ca.h ca_factor_init"
  ca_factor_init :: Ptr CCaFactor -> Ptr CCaCtx -> IO ()

-- | /ca_factor_clear/ /fac/ /ctx/ 
--
-- Clears the factorization structure /fac/.
foreign import ccall "ca.h ca_factor_clear"
  ca_factor_clear :: Ptr CCaFactor -> Ptr CCaCtx -> IO ()

foreign import ccall "ca.h &ca_factor_clear"
  p_ca_factor_clear :: FunPtr (Ptr CCaFactor -> Ptr CCaCtx -> IO ())

-- | /ca_factor_one/ /fac/ /ctx/ 
--
-- Sets /fac/ to the empty factorization (equivalent to the number 1).
foreign import ccall "ca.h ca_factor_one"
  ca_factor_one :: Ptr CCaFactor -> Ptr CCaCtx -> IO ()

-- | /ca_factor_print/ /fac/ /ctx/ 
--
-- Prints a description of /fac/ to standard output.
foreign import ccall "ca.h ca_factor_print"
  ca_factor_print :: Ptr CCaFactor -> Ptr CCaCtx -> IO ()

-- | /ca_factor_insert/ /fac/ /base/ /exp/ /ctx/ 
--
-- Inserts \(b^e\) into /fac/ where /b/ is given by /base/ and /e/ is given
-- by /exp/. If a base element structurally identical to /base/ already
-- exists in /fac/, the corresponding exponent is incremented by /exp/;
-- otherwise, this factor is appended.
foreign import ccall "ca.h ca_factor_insert"
  ca_factor_insert :: Ptr CCaFactor -> Ptr CCa -> Ptr CCa -> Ptr CCaCtx -> IO ()

-- | /ca_factor_get_ca/ /res/ /fac/ /ctx/ 
--
-- Expands /fac/ back to a single @ca_t@ by evaluating the powers and
-- multiplying out the result.
foreign import ccall "ca.h ca_factor_get_ca"
  ca_factor_get_ca :: Ptr CCa -> Ptr CCaFactor -> Ptr CCaCtx -> IO ()

-- | /ca_factor/ /res/ /x/ /flags/ /ctx/ 
--
-- Sets /res/ to a factorization of /x/ of the form
-- \(x = b_1^{e_1} b_2^{e_2} \cdots b_n^{e_n}\). Requires that /x/ is not a
-- special value. The type of factorization is controlled by /flags/, which
-- can be set to a combination of constants in the following section.
foreign import ccall "ca.h ca_factor"
  ca_factor :: Ptr CCaFactor -> Ptr CCa -> CULong -> Ptr CCaCtx -> IO ()

-- Factorization options -------------------------------------------------------

-- $factorization_options
-- The following flags select the structural polynomial factorization
-- to perform over formal fields \(\mathbb{Q}(a_1,\ldots,a_n)\). Each
-- flag in the list strictly encompasses the factorization power of
-- the preceding flag, so it is unnecessary to pass more than one
-- flag.

type CaFactorOption = CULong

ca_factor_poly_none, ca_factor_poly_content, ca_factor_poly_sqf, ca_factor_poly_full, ca_factor_zz_none, ca_factor_zz_smooth, ca_factor_zz_full :: CaFactorOption

-- | /ca_factor_poly_none/
-- 
-- No polynomial factorization at all.
-- 
ca_factor_poly_none = #const CA_FACTOR_POLY_NONE
-- | /ca_factor_poly_content/
-- 
-- Only extract the rational content.
-- 
ca_factor_poly_content = #const CA_FACTOR_POLY_CONTENT
-- | /ca_factor_poly_sqf/
-- 
-- Perform a squarefree factorization in addition to extracting
-- the rational content.
-- 
ca_factor_poly_sqf = #const CA_FACTOR_POLY_SQF
-- | /ca_factor_poly_full/
-- 
-- Perform a full multivariate polynomial factorization.
-- 
-- The following flags select the factorization to perform over `\mathbb{Z}`.
-- Integer factorization is applied if *x* is an element of `\mathbb{Q}`, and to
-- the extracted rational content of polynomials.
-- Each flag in the list strictly encompasses the factorization power of
-- the preceding flag, so it is unnecessary to pass more than one flag.
-- 
ca_factor_poly_full = #const CA_FACTOR_POLY_FULL
-- | /ca_factor_zz_none/
-- 
-- No integer factorization at all.
-- 
ca_factor_zz_none = #const CA_FACTOR_ZZ_NONE
-- | /ca_factor_zz_smooth/
-- 
-- Perform a smooth factorization to extract small prime factors
-- (heuristically up to ``CA_OPT_SMOOTH_LIMIT`` bits) in addition to
-- identifying perfect powers.
-- 
ca_factor_zz_smooth = #const CA_FACTOR_ZZ_SMOOTH
-- | /ca_factor_zz_full/
-- 
-- Perform a complete integer factorization into prime numbers.
-- This is prohibitively slow for general integers exceeding 70-80 digits.
ca_factor_zz_full = #const CA_FACTOR_ZZ_FULL

-- The following flags select the factorization to perform over
-- \(\mathbb{Z}\). Integer factorization is applied if /x/ is an element of
-- \(\mathbb{Q}\), and to the extracted rational content of polynomials.
-- Each flag in the list strictly encompasses the factorization power of
-- the preceding flag, so it is unnecessary to pass more than one flag.

-- Context options -------------------------------------------------------------

-- $context_options
-- The /options/ member of a @CaCtx@ object is an array of /slong/
-- values controlling simplification behavior and various other settings.
-- The values of the array at the following indices can be changed by the
-- user (example: @ctx->options[CA_OPT_PREC_LIMIT] = 65536@).
--
-- It is recommended to set options controlling evaluation only at the time
-- when a context object is created. Changing such options later should
-- normally be harmless, but since the update will not apply retroactively
-- to objects that have already been computed and cached, one might not see
-- the expected behavior. Superficial options (printing) can be changed at
-- any time.

type CaOption = CULong

ca_opt_verbose, ca_opt_print_flags, ca_opt_mpoly_ord, ca_opt_prec_limit, ca_opt_qqbar_deg_limit, ca_opt_low_prec, ca_opt_smooth_limit, ca_opt_lll_prec, ca_opt_pow_limit, ca_opt_use_groebner, ca_opt_groebner_length_limit, ca_opt_groebner_poly_length_limit, ca_opt_groebner_poly_bits_limit, ca_opt_vieta_limit, ca_opt_trig_form, ca_trig_direct, ca_trig_exponential, ca_trig_sine_cosine, ca_trig_tangent :: CaOption

-- | /ca_opt_verbose/
-- 
-- Whether to print debug information. Default value: 0.
-- 
ca_opt_verbose = #const CA_OPT_VERBOSE
-- | /ca_opt_print_flags/
-- 
-- Printing style. See :ref:`ca-printing` for details.
-- Default value: ``CA_PRINT_DEFAULT``.
-- 
ca_opt_print_flags = #const CA_OPT_PRINT_FLAGS
-- | /ca_opt_mpoly_ord/
-- 
-- Monomial ordering to use for multivariate polynomials. Possible
-- values are ``ORD_LEX``, ``ORD_DEGLEX`` and ``ORD_DEGREVLEX``.
-- Default value: ``ORD_LEX``.
-- This option must be set before doing any computations.
-- 
ca_opt_mpoly_ord = #const CA_OPT_MPOLY_ORD
-- | /ca_opt_prec_limit/
-- 
-- Maximum precision to use internally for numerical evaluation with Arb,
-- and in some cases for the magntiude of exact coefficients.
-- This parameter affects the possibility to prove inequalities
-- and find simplifications between related extension numbers.
-- This is not a strict limit; some calculations may use higher precision
-- when there is a good reason to do so.
-- Default value: 4096.
-- 
ca_opt_prec_limit = #const CA_OPT_PREC_LIMIT
-- | /ca_opt_qqbar_deg_limit/
-- 
-- Maximum degree of :type:`qqbar_t` elements allowed internally during
-- simplification of algebraic numbers. This limit may be exceeded
-- when the user provides explicit :type:`qqbar_t` input of higher degree.
-- Default value: 120.
-- 
ca_opt_qqbar_deg_limit = #const CA_OPT_QQBAR_DEG_LIMIT
-- | /ca_opt_low_prec/
-- 
-- Numerical precision to use for fast checks (typically, before attempting
-- more expensive operations). Default value: 64.
-- 
ca_opt_low_prec = #const CA_OPT_LOW_PREC
-- | /ca_opt_smooth_limit/
-- 
-- Size in bits for factors in smooth integer factorization. Default value: 32.
-- 
ca_opt_smooth_limit = #const CA_OPT_SMOOTH_LIMIT
-- | /ca_opt_lll_prec/
-- 
-- Precision to use to find integer relations using LLL. Default value: 128.
-- 
ca_opt_lll_prec = #const CA_OPT_LLL_PREC
-- | /ca_opt_pow_limit/
-- 
-- Largest exponent to expand powers automatically. This only applies
-- in multivariate and transcendental fields: in number fields,
-- ``CA_OPT_PREC_LIMIT`` applies instead. Default value: 20.
-- 
ca_opt_pow_limit = #const CA_OPT_POW_LIMIT
-- | /ca_opt_use_groebner/
-- 
-- Boolean flag for whether to use Gröbner basis computation.
-- This flag and the following limits affect the ability to
-- prove multivariate identities.
-- Default value: 1.
-- 
ca_opt_use_groebner = #const CA_OPT_USE_GROEBNER
-- | /ca_opt_groebner_length_limit/
-- 
-- Maximum length of ideal basis allowed in Buchberger's algorithm.
-- Default value: 100.
-- 
ca_opt_groebner_length_limit = #const CA_OPT_GROEBNER_LENGTH_LIMIT
-- | /ca_opt_groebner_poly_length_limit/
-- 
-- Maximum length of polynomials allowed in Buchberger's algorithm.
-- Default value: 1000.
-- 
ca_opt_groebner_poly_length_limit = #const CA_OPT_GROEBNER_POLY_LENGTH_LIMIT
-- | /ca_opt_groebner_poly_bits_limit/
-- 
-- Maximum coefficient size in bits of polynomials allowed in
-- Buchberger's algorithm.
-- Default value: 10000.
-- 
ca_opt_groebner_poly_bits_limit = #const CA_OPT_GROEBNER_POLY_BITS_LIMIT
-- | /ca_opt_vieta_limit/
-- 
-- Maximum degree *n* of algebraic numbers for which to add Vieta's
-- formulas to the reduction ideal.
-- This must be set relatively low
-- since the number of terms in Vieta's formulas is `O(2^n)`
-- and the resulting Gröbner basis computations can be expensive.
-- Default value: 6.
-- 
ca_opt_vieta_limit = #const CA_OPT_VIETA_LIMIT
-- | /ca_opt_trig_form/
-- 
-- Default representation of trigonometric functions.
--
-- Default value: ``ca_trig_exponential``.
-- 
-- The *exponential* representation is currently used by default
-- as typically works best for field arithmetic
-- and simplifications, although it has the disadvantage of
-- introducing complex numbers where real numbers would be sufficient.
-- This may change in the future.
--
-- The following values are possible:
ca_opt_trig_form = #const CA_OPT_TRIG_FORM
-- | /ca_trig_direct/
-- 
-- Use the direct functions (with some exceptions).
-- 
ca_trig_direct = #const CA_TRIG_DIRECT
-- | /ca_trig_exponential/
-- 
-- Use complex exponentials.
-- 
ca_trig_exponential = #const CA_TRIG_EXPONENTIAL
-- | /ca_trig_sine_cosine/
-- 
-- Use sines and cosines.
-- 
ca_trig_sine_cosine = #const CA_TRIG_SINE_COSINE
-- | /ca_trig_tangent/
-- 
-- Use tangents.
-- 
ca_trig_tangent = #const CA_TRIG_TANGENT

-- Internal representation -----------------------------------------------------

-- | /_ca_make_field_element/ /x/ /new_index/ /ctx/ 
--
-- Changes the internal representation of /x/ to that of an element of the
-- field with index /new_index/ in the context object /ctx/. This may
-- destroy the value of /x/.
foreign import ccall "ca.h _ca_make_field_element"
  _ca_make_field_element :: Ptr CCa -> Ptr CCaField -> Ptr CCaCtx -> IO ()

-- | /_ca_make_fmpq/ /x/ /ctx/ 
--
-- Changes the internal representation of /x/ to that of an element of the
-- trivial field \(\mathbb{Q}\). This may destroy the value of /x/.
foreign import ccall "ca.h _ca_make_fmpq"
  _ca_make_fmpq :: Ptr CCa -> Ptr CCaCtx -> IO ()




