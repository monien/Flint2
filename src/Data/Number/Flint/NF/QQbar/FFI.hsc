{-# language
    CApiFFI
  , FlexibleInstances
  , ForeignFunctionInterface
  , MultiParamTypeClasses
  , TupleSections
  , TypeFamilies
  , ScopedTypeVariables
  #-}

module Data.Number.Flint.NF.QQbar.FFI (
  -- * Algebraic numbers represented by minimal polynomials
  -- * Types
    QQbar (..)
  , CQQbar (..)
  , newQQbar
  , withQQbar
  , withNewQQbar
  -- * Memory management
  , qqbar_init
  , qqbar_clear
  , _qqbar_vec_init
  , _qqbar_vec_clear
  -- * Assignment
  , qqbar_swap
  , qqbar_set
  , qqbar_set_re_im
  , qqbar_set_d
  -- * Properties
  , qqbar_degree
  , qqbar_is_rational
  , qqbar_is_integer
  , qqbar_is_algebraic_integer
  , qqbar_is_zero
  , qqbar_is_i
  , qqbar_is_real
  , qqbar_height
  , qqbar_height_bits
  , qqbar_within_limits
  , qqbar_binop_within_limits
  -- * Conversions
  , _qqbar_get_fmpq
  , qqbar_get_fmpq
  , qqbar_get_fmpz
  -- * Special values
  , qqbar_zero
  , qqbar_one
  , qqbar_i
  , qqbar_phi
  -- * Input and output
  , qqbar_print
  , qqbar_printn
  , qqbar_printnd
  -- * Random generation
  , qqbar_randtest
  , qqbar_randtest_real
  , qqbar_randtest_nonreal
  -- * Comparisons
  , qqbar_equal
  , qqbar_equal_fmpq_poly_val
  , qqbar_cmp_re
  , qqbar_cmp_im
  , qqbar_cmpabs_re
  , qqbar_cmpabs_im
  , qqbar_cmpabs
  , qqbar_cmp_root_order
  , qqbar_hash
  -- * Complex parts
  , qqbar_conj
  , qqbar_re
  , qqbar_im
  , qqbar_re_im
  , qqbar_abs
  , qqbar_abs2
  , qqbar_sgn
  , qqbar_sgn_re
  , qqbar_sgn_im
  , qqbar_csgn
  -- * Integer parts
  , qqbar_floor
  , qqbar_ceil
  -- * Arithmetic
  , qqbar_neg
  , qqbar_add
  , qqbar_sub
  , qqbar_mul
  , qqbar_mul_2exp_si
  , qqbar_sqr
  , qqbar_inv
  , qqbar_div
  , qqbar_scalar_op
  -- * Powers and roots
  , qqbar_sqrt
  , qqbar_rsqrt
  , qqbar_pow_ui
  , qqbar_root_ui
  , qqbar_fmpq_pow_si_ui
  , qqbar_pow
  -- * Numerical enclosures
  , qqbar_get_acb
  , qqbar_get_arb
  , qqbar_get_arb_re
  , qqbar_get_arb_im
  , qqbar_cache_enclosure
  -- * Numerator and denominator
  , qqbar_denominator
  , qqbar_numerator
  -- * Conjugates
  , qqbar_conjugates
  -- * Polynomial evaluation
  , _qqbar_evaluate_fmpq_poly
  , qqbar_evaluate_fmpz_mpoly_iter
  -- * Polynomial roots
  , qqbar_roots_fmpz_poly
  , qqbar_eigenvalues_fmpz_mat
  -- * Roots of unity and trigonometric functions
  , qqbar_root_of_unity
  , qqbar_is_root_of_unity
  , qqbar_exp_pi_i
  , qqbar_cos_pi
  , qqbar_log_pi_i
  , qqbar_atan_pi
  , qqbar_asin_pi
  , qqbar_acos_pi
  , qqbar_acot_pi
  , qqbar_asec_pi
  , qqbar_acsc_pi
  -- * Guessing and simplification
  , qqbar_guess
  , qqbar_express_in_field
  -- * Symbolic expressions and conversion to radicals
  , qqbar_get_quadratic
  , qqbar_set_fexpr
  , qqbar_get_fexpr_repr
  , qqbar_get_fexpr_root_nearest
  , qqbar_get_fexpr_root_indexed
  , qqbar_get_fexpr_formula
  -- * Internal functions
  , qqbar_fmpz_poly_composed_op
  , qqbar_binary_op
  , _qqbar_validate_uniqueness
  , _qqbar_validate_existence_uniqueness
  , _qqbar_enclosure_raw
  , _qqbar_acb_lindep
) where 

-- Algebraic numbers represented by minimal polynomials ------------------------

import Foreign.Ptr
import Foreign.ForeignPtr
import Foreign.Storable
import Foreign.C.Types
import Foreign.C.String
import Foreign.Marshal.Alloc

import Data.Number.Flint.Flint
import Data.Number.Flint.Fmpz
import Data.Number.Flint.Fmpz.Mat
import Data.Number.Flint.Fmpz.Poly
import Data.Number.Flint.Fmpz.MPoly

import Data.Number.Flint.Fmpq
import Data.Number.Flint.Fmpq.Poly

import Data.Number.Flint.Arb.Types
import Data.Number.Flint.Acb.Types

#include <flint/qqbar.h>

-- qq_bar_t --------------------------------------------------------------------

data QQbar = QQbar {-# UNPACK #-} !(ForeignPtr CQQbar) 
type CQQbar = CFlint QQbar

instance Storable CQQbar where
  {-# INLINE sizeOf #-}
  sizeOf    _ = #{size      qqbar_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment qqbar_t}
  peek = undefined
  poke = undefined
  
-- | Create a QQbar.
newQQbar = do
  p <- mallocForeignPtr
  withForeignPtr p qqbar_init
  addForeignPtrFinalizer p_qqbar_clear p
  return $ QQbar p

-- | Use QQbar in `f`.
{-# INLINE withQQbar #-}
withQQbar (QQbar p) f = do
  withForeignPtr p $ \fp -> (QQbar p,) <$> f fp

-- | Apply `f` to new QQbar.
{-# INLINE withNewQQbar #-}
withNewQQbar f = do
  x <- newQQbar
  withQQbar x f

-- Memory management -----------------------------------------------------------

-- | /qqbar_init/ /res/ 
-- 
-- Initializes the variable /res/ for use, and sets its value to zero.
foreign import ccall "qqbar.h qqbar_init"
  qqbar_init :: Ptr CQQbar -> IO ()

-- | /qqbar_clear/ /res/ 
-- 
-- Clears the variable /res/, freeing or recycling its allocated memory.
foreign import ccall "qqbar.h qqbar_clear"
  qqbar_clear :: Ptr CQQbar -> IO ()

foreign import ccall "qqbar.h &qqbar_clear"
  p_qqbar_clear :: FunPtr (Ptr CQQbar -> IO ())

-- | /_qqbar_vec_init/ /len/ 
-- 
-- Returns a pointer to an array of /len/ initialized /qqbar_struct/:s.
foreign import ccall "qqbar.h _qqbar_vec_init"
  _qqbar_vec_init :: CLong -> IO (Ptr CQQbar)

-- | /_qqbar_vec_clear/ /vec/ /len/ 
-- 
-- Clears all /len/ entries in the vector /vec/ and frees the vector
-- itself.
foreign import ccall "qqbar.h _qqbar_vec_clear"
  _qqbar_vec_clear :: Ptr CQQbar -> CLong -> IO ()

-- Assignment ------------------------------------------------------------------

-- | /qqbar_swap/ /x/ /y/ 
-- 
-- Swaps the values of /x/ and /y/ efficiently.
foreign import ccall "qqbar.h qqbar_swap"
  qqbar_swap :: Ptr CQQbar -> Ptr CQQbar -> IO ()

-- | /qqbar_set/ /res/ /x/ 
-- 
-- Sets /res/ to the value /x/.
foreign import ccall "qqbar.h qqbar_set"
  qqbar_set :: Ptr CQQbar -> Ptr CQQbar -> IO ()

-- | /qqbar_set_re_im/ /res/ /x/ /y/ 
-- 
-- Sets /res/ to the value \(x + yi\).
foreign import ccall "qqbar.h qqbar_set_re_im"
  qqbar_set_re_im :: Ptr CQQbar -> Ptr CQQbar -> Ptr CQQbar -> IO ()

-- | /qqbar_set_d/ /res/ /x/ 
-- 
-- Sets /res/ to the value /x/ or \(x + yi\) respectively. These functions
-- performs error handling: if /x/ and /y/ are finite, the conversion
-- succeeds and the return flag is 1. If /x/ or /y/ is non-finite (infinity
-- or NaN), the conversion fails and the return flag is 0.
foreign import ccall "qqbar.h qqbar_set_d"
  qqbar_set_d :: Ptr CQQbar -> CDouble -> IO CInt

-- Properties ------------------------------------------------------------------

-- | /qqbar_degree/ /x/ 
-- 
-- Returns the degree of /x/, i.e. the degree of the minimal polynomial.
foreign import ccall "qqbar.h qqbar_degree"
  qqbar_degree :: Ptr CQQbar -> IO CLong

-- | /qqbar_is_rational/ /x/ 
-- 
-- Returns whether /x/ is a rational number.
foreign import ccall "qqbar.h qqbar_is_rational"
  qqbar_is_rational :: Ptr CQQbar -> IO CInt

-- | /qqbar_is_integer/ /x/ 
-- 
-- Returns whether /x/ is an integer (an element of \(\mathbb{Z}\)).
foreign import ccall "qqbar.h qqbar_is_integer"
  qqbar_is_integer :: Ptr CQQbar -> IO CInt

-- | /qqbar_is_algebraic_integer/ /x/ 
-- 
-- Returns whether /x/ is an algebraic integer, i.e. whether its minimal
-- polynomial has leading coefficient 1.
foreign import ccall "qqbar.h qqbar_is_algebraic_integer"
  qqbar_is_algebraic_integer :: Ptr CQQbar -> IO CInt

-- | /qqbar_is_zero/ /x/ 
-- 
-- Returns whether /x/ is the number \(0\), \(1\), \(-1\).
foreign import ccall "qqbar.h qqbar_is_zero"
  qqbar_is_zero :: Ptr CQQbar -> IO CInt

-- | /qqbar_is_i/ /x/ 
-- 
-- Returns whether /x/ is the imaginary unit \(i\) (respectively \(-i\)).
foreign import ccall "qqbar.h qqbar_is_i"
  qqbar_is_i :: Ptr CQQbar -> IO CInt

-- | /qqbar_is_real/ /x/ 
-- 
-- Returns whether /x/ is a real number.
foreign import ccall "qqbar.h qqbar_is_real"
  qqbar_is_real :: Ptr CQQbar -> IO CInt

-- | /qqbar_height/ /res/ /x/ 
-- 
-- Sets /res/ to the height of /x/ (the largest absolute value of the
-- coefficients of the minimal polynomial of /x/).
foreign import ccall "qqbar.h qqbar_height"
  qqbar_height :: Ptr CFmpz -> Ptr CQQbar -> IO ()

-- | /qqbar_height_bits/ /x/ 
-- 
-- Returns the height of /x/ (the largest absolute value of the
-- coefficients of the minimal polynomial of /x/) measured in bits.
foreign import ccall "qqbar.h qqbar_height_bits"
  qqbar_height_bits :: Ptr CQQbar -> IO CLong

-- | /qqbar_within_limits/ /x/ /deg_limit/ /bits_limit/ 
-- 
-- Checks if /x/ has degree bounded by /deg_limit/ and height bounded by
-- /bits_limit/ bits, returning 0 (false) or 1 (true). If /deg_limit/ is
-- set to 0, the degree check is skipped, and similarly for /bits_limit/.
foreign import ccall "qqbar.h qqbar_within_limits"
  qqbar_within_limits :: Ptr CQQbar -> CLong -> CLong -> IO CInt

-- | /qqbar_binop_within_limits/ /x/ /y/ /deg_limit/ /bits_limit/ 
-- 
-- Checks if \(x + y\), \(x - y\), \(x \cdot y\) and \(x / y\) certainly
-- have degree bounded by /deg_limit/ (by multiplying the degrees for /x/
-- and /y/ to obtain a trivial bound). For /bits_limits/, the sum of the
-- bit heights of /x/ and /y/ is checked against the bound (this is only a
-- heuristic). If /deg_limit/ is set to 0, the degree check is skipped, and
-- similarly for /bits_limit/.
foreign import ccall "qqbar.h qqbar_binop_within_limits"
  qqbar_binop_within_limits :: Ptr CQQbar -> Ptr CQQbar -> CLong -> CLong -> IO CInt

-- Conversions -----------------------------------------------------------------

-- | /_qqbar_get_fmpq/ /num/ /den/ /x/ 
-- 
-- Sets /num/ and /den/ to the numerator and denominator of /x/. Aborts if
-- /x/ is not a rational number.
foreign import ccall "qqbar.h _qqbar_get_fmpq"
  _qqbar_get_fmpq :: Ptr CFmpz -> Ptr CFmpz -> Ptr CQQbar -> IO ()

-- | /qqbar_get_fmpq/ /res/ /x/ 
-- 
-- Sets /res/ to /x/. Aborts if /x/ is not a rational number.
foreign import ccall "qqbar.h qqbar_get_fmpq"
  qqbar_get_fmpq :: Ptr CFmpq -> Ptr CQQbar -> IO ()

-- | /qqbar_get_fmpz/ /res/ /x/ 
-- 
-- Sets /res/ to /x/. Aborts if /x/ is not an integer.
foreign import ccall "qqbar.h qqbar_get_fmpz"
  qqbar_get_fmpz :: Ptr CFmpz -> Ptr CQQbar -> IO ()

-- Special values --------------------------------------------------------------

-- | /qqbar_zero/ /res/ 
-- 
-- Sets /res/ to the number 0.
foreign import ccall "qqbar.h qqbar_zero"
  qqbar_zero :: Ptr CQQbar -> IO ()

-- | /qqbar_one/ /res/ 
-- 
-- Sets /res/ to the number 1.
foreign import ccall "qqbar.h qqbar_one"
  qqbar_one :: Ptr CQQbar -> IO ()

-- | /qqbar_i/ /res/ 
-- 
-- Sets /res/ to the imaginary unit \(i\).
foreign import ccall "qqbar.h qqbar_i"
  qqbar_i :: Ptr CQQbar -> IO ()

-- | /qqbar_phi/ /res/ 
-- 
-- Sets /res/ to the golden ratio \(\varphi = \tfrac{1}{2}(\sqrt{5} + 1)\).
foreign import ccall "qqbar.h qqbar_phi"
  qqbar_phi :: Ptr CQQbar -> IO ()

-- Input and output ------------------------------------------------------------

foreign import ccall "qqbar.h qqbar_get_str"
  qqbar_get_str :: Ptr CQQbar -> IO CString

foreign import ccall "qqbar.h qqbar_get_strn"
  qqbar_get_strn :: Ptr CQQbar -> CLong -> IO CString

foreign import ccall "qqbar.h qqbar_get_strd"
  qqbar_get_strd :: Ptr CQQbar -> CLong -> IO CString
 
-- | /qqbar_print/ /x/ 
-- 
-- Prints /res/ to standard output. The output shows the degree and the
-- list of coefficients of the minimal polynomial followed by a decimal
-- representation of the enclosing interval. This function is mainly
-- intended for debugging.
qqbar_print :: Ptr CQQbar -> IO ()
qqbar_print x = do
  cs <- qqbar_get_str x
  s <- peekCString cs
  free cs
  putStr s
  
-- | /qqbar_printn/ /x/ /n/ 
-- 
-- Prints /res/ to standard output. The output shows a decimal
-- approximation to /n/ digits.
qqbar_printn :: Ptr CQQbar -> CLong -> IO ()
qqbar_printn x digits = do
  cs <- qqbar_get_strn x digits
  s <- peekCString cs
  free cs
  putStr s
  
-- | /qqbar_printnd/ /x/ /n/ 
-- 
-- Prints /res/ to standard output. The output shows a decimal
-- approximation to /n/ digits, followed by the degree of the number.
qqbar_printnd :: Ptr CQQbar -> CLong -> IO ()
qqbar_printnd x digits = do
  cs <- qqbar_get_strn x digits
  s <- peekCString cs
  free cs
  putStr s
 
-- For example, /print/, /printn/ and /printnd/ with \(n = 6\) give the
-- following output for the numbers 0, 1, \(i\), \(\varphi\),
-- \(\sqrt{2}-\sqrt{3} i\):
--
-- Random generation -----------------------------------------------------------

-- | /qqbar_randtest/ /res/ /state/ /deg/ /bits/ 
-- 
-- Sets /res/ to a random algebraic number with degree up to /deg/ and with
-- height (measured in bits) up to /bits/.
foreign import ccall "qqbar.h qqbar_randtest"
  qqbar_randtest :: Ptr CQQbar -> Ptr CFRandState -> CLong -> CLong -> IO ()

-- | /qqbar_randtest_real/ /res/ /state/ /deg/ /bits/ 
-- 
-- Sets /res/ to a random real algebraic number with degree up to /deg/ and
-- with height (measured in bits) up to /bits/.
foreign import ccall "qqbar.h qqbar_randtest_real"
  qqbar_randtest_real :: Ptr CQQbar -> Ptr CFRandState -> CLong -> CLong -> IO ()

-- | /qqbar_randtest_nonreal/ /res/ /state/ /deg/ /bits/ 
-- 
-- Sets /res/ to a random nonreal algebraic number with degree up to /deg/
-- and with height (measured in bits) up to /bits/. Since all algebraic
-- numbers of degree 1 are real, /deg/ must be at least 2.
foreign import ccall "qqbar.h qqbar_randtest_nonreal"
  qqbar_randtest_nonreal :: Ptr CQQbar -> Ptr CFRandState -> CLong -> CLong -> IO ()

-- Comparisons -----------------------------------------------------------------

-- | /qqbar_equal/ /x/ /y/ 
-- 
-- Returns whether /x/ and /y/ are equal.
foreign import ccall "qqbar.h qqbar_equal"
  qqbar_equal :: Ptr CQQbar -> Ptr CQQbar -> IO CInt

-- | /qqbar_equal_fmpq_poly_val/ /x/ /f/ /y/ 
-- 
-- Returns whether /x/ is equal to \(f(y)\). This function is more
-- efficient than evaluating \(f(y)\) and comparing the results.
foreign import ccall "qqbar.h qqbar_equal_fmpq_poly_val"
  qqbar_equal_fmpq_poly_val :: Ptr CQQbar -> Ptr CFmpqPoly -> Ptr CQQbar -> IO CInt

-- | /qqbar_cmp_re/ /x/ /y/ 
-- 
-- Compares the real parts of /x/ and /y/, returning -1, 0 or +1.
foreign import ccall "qqbar.h qqbar_cmp_re"
  qqbar_cmp_re :: Ptr CQQbar -> Ptr CQQbar -> IO CInt

-- | /qqbar_cmp_im/ /x/ /y/ 
-- 
-- Compares the imaginary parts of /x/ and /y/, returning -1, 0 or +1.
foreign import ccall "qqbar.h qqbar_cmp_im"
  qqbar_cmp_im :: Ptr CQQbar -> Ptr CQQbar -> IO CInt

-- | /qqbar_cmpabs_re/ /x/ /y/ 
-- 
-- Compares the absolute values of the real parts of /x/ and /y/, returning
-- -1, 0 or +1.
foreign import ccall "qqbar.h qqbar_cmpabs_re"
  qqbar_cmpabs_re :: Ptr CQQbar -> Ptr CQQbar -> IO CInt

-- | /qqbar_cmpabs_im/ /x/ /y/ 
-- 
-- Compares the absolute values of the imaginary parts of /x/ and /y/,
-- returning -1, 0 or +1.
foreign import ccall "qqbar.h qqbar_cmpabs_im"
  qqbar_cmpabs_im :: Ptr CQQbar -> Ptr CQQbar -> IO CInt

-- | /qqbar_cmpabs/ /x/ /y/ 
-- 
-- Compares the absolute values of /x/ and /y/, returning -1, 0 or +1.
foreign import ccall "qqbar.h qqbar_cmpabs"
  qqbar_cmpabs :: Ptr CQQbar -> Ptr CQQbar -> IO CInt

-- | /qqbar_cmp_root_order/ /x/ /y/ 
-- 
-- Compares /x/ and /y/ using an arbitrary but convenient ordering defined
-- on the complex numbers. This is useful for sorting the roots of a
-- polynomial in a canonical order.
-- 
-- We define the root order as follows: real roots come first, in
-- descending order. Nonreal roots are subsequently ordered first by real
-- part in descending order, then in ascending order by the absolute value
-- of the imaginary part, and then in descending order of the sign. This
-- implies that complex conjugate roots are adjacent, with the root in the
-- upper half plane first.
foreign import ccall "qqbar.h qqbar_cmp_root_order"
  qqbar_cmp_root_order :: Ptr CQQbar -> Ptr CQQbar -> IO CInt

-- | /qqbar_hash/ /x/ 
-- 
-- Returns a hash of /x/. As currently implemented, this function only
-- hashes the minimal polynomial of /x/. The user should mix in some bits
-- based on the numerical value if it is critical to distinguish between
-- conjugates of the same minimal polynomial. This function is also likely
-- to produce serial runs of values for lexicographically close minimal
-- polynomials. This is not necessarily a problem for use in hash tables,
-- but if it is important that all bits in the output are random, the user
-- should apply an integer hash function to the output.
foreign import ccall "qqbar.h qqbar_hash"
  qqbar_hash :: Ptr CQQbar -> IO CULong

-- Complex parts ---------------------------------------------------------------

-- | /qqbar_conj/ /res/ /x/ 
-- 
-- Sets /res/ to the complex conjugate of /x/.
foreign import ccall "qqbar.h qqbar_conj"
  qqbar_conj :: Ptr CQQbar -> Ptr CQQbar -> IO ()

-- | /qqbar_re/ /res/ /x/ 
-- 
-- Sets /res/ to the real part of /x/.
foreign import ccall "qqbar.h qqbar_re"
  qqbar_re :: Ptr CQQbar -> Ptr CQQbar -> IO ()

-- | /qqbar_im/ /res/ /x/ 
-- 
-- Sets /res/ to the imaginary part of /x/.
foreign import ccall "qqbar.h qqbar_im"
  qqbar_im :: Ptr CQQbar -> Ptr CQQbar -> IO ()

-- | /qqbar_re_im/ /res1/ /res2/ /x/ 
-- 
-- Sets /res1/ to the real part of /x/ and /res2/ to the imaginary part of
-- /x/.
foreign import ccall "qqbar.h qqbar_re_im"
  qqbar_re_im :: Ptr CQQbar -> Ptr CQQbar -> Ptr CQQbar -> IO ()

-- | /qqbar_abs/ /res/ /x/ 
-- 
-- Sets /res/ to the absolute value of /x/:
foreign import ccall "qqbar.h qqbar_abs"
  qqbar_abs :: Ptr CQQbar -> Ptr CQQbar -> IO ()

-- | /qqbar_abs2/ /res/ /x/ 
-- 
-- Sets /res/ to the square of the absolute value of /x/.
foreign import ccall "qqbar.h qqbar_abs2"
  qqbar_abs2 :: Ptr CQQbar -> Ptr CQQbar -> IO ()

-- | /qqbar_sgn/ /res/ /x/ 
-- 
-- Sets /res/ to the complex sign of /x/, defined as 0 if /x/ is zero and
-- as \(x / |x|\) otherwise.
foreign import ccall "qqbar.h qqbar_sgn"
  qqbar_sgn :: Ptr CQQbar -> Ptr CQQbar -> IO ()

-- | /qqbar_sgn_re/ /x/ 
-- 
-- Returns the sign of the real part of /x/ (-1, 0 or +1).
foreign import ccall "qqbar.h qqbar_sgn_re"
  qqbar_sgn_re :: Ptr CQQbar -> IO CInt

-- | /qqbar_sgn_im/ /x/ 
-- 
-- Returns the sign of the imaginary part of /x/ (-1, 0 or +1).
foreign import ccall "qqbar.h qqbar_sgn_im"
  qqbar_sgn_im :: Ptr CQQbar -> IO CInt

-- | /qqbar_csgn/ /x/ 
-- 
-- Returns the extension of the real sign function taking the value 1 for
-- /x/ strictly in the right half plane, -1 for /x/ strictly in the left
-- half plane, and the sign of the imaginary part when /x/ is on the
-- imaginary axis. Equivalently,
-- \(\operatorname{csgn}(x) = x / \sqrt{x^2}\) except that the value is 0
-- when /x/ is zero.
foreign import ccall "qqbar.h qqbar_csgn"
  qqbar_csgn :: Ptr CQQbar -> IO CInt

-- Integer parts ---------------------------------------------------------------

-- | /qqbar_floor/ /res/ /x/ 
-- 
-- Sets /res/ to the floor function of /x/. If /x/ is not real, the value
-- is defined as the floor function of the real part of /x/.
foreign import ccall "qqbar.h qqbar_floor"
  qqbar_floor :: Ptr CFmpz -> Ptr CQQbar -> IO ()

-- | /qqbar_ceil/ /res/ /x/ 
-- 
-- Sets /res/ to the ceiling function of /x/. If /x/ is not real, the value
-- is defined as the ceiling function of the real part of /x/.
foreign import ccall "qqbar.h qqbar_ceil"
  qqbar_ceil :: Ptr CFmpz -> Ptr CQQbar -> IO ()

-- Arithmetic ------------------------------------------------------------------

-- | /qqbar_neg/ /res/ /x/ 
-- 
-- Sets /res/ to the negation of /x/.
foreign import ccall "qqbar.h qqbar_neg"
  qqbar_neg :: Ptr CQQbar -> Ptr CQQbar -> IO ()

-- | /qqbar_add/ /res/ /x/ /y/ 
-- 
-- Sets /res/ to the sum of /x/ and /y/.
foreign import ccall "qqbar.h qqbar_add"
  qqbar_add :: Ptr CQQbar -> Ptr CQQbar -> Ptr CQQbar -> IO ()

-- | /qqbar_sub/ /res/ /x/ /y/ 
-- 
-- Sets /res/ to the difference of /x/ and /y/.
foreign import ccall "qqbar.h qqbar_sub"
  qqbar_sub :: Ptr CQQbar -> Ptr CQQbar -> Ptr CQQbar -> IO ()

-- | /qqbar_mul/ /res/ /x/ /y/ 
-- 
-- Sets /res/ to the product of /x/ and /y/.
foreign import ccall "qqbar.h qqbar_mul"
  qqbar_mul :: Ptr CQQbar -> Ptr CQQbar -> Ptr CQQbar -> IO ()

-- | /qqbar_mul_2exp_si/ /res/ /x/ /e/ 
-- 
-- Sets /res/ to /x/ multiplied by \(2^e\).
foreign import ccall "qqbar.h qqbar_mul_2exp_si"
  qqbar_mul_2exp_si :: Ptr CQQbar -> Ptr CQQbar -> CLong -> IO ()

-- | /qqbar_sqr/ /res/ /x/ 
-- 
-- Sets /res/ to the square of /x/.
foreign import ccall "qqbar.h qqbar_sqr"
  qqbar_sqr :: Ptr CQQbar -> Ptr CQQbar -> IO ()

-- | /qqbar_inv/ /res/ /x/ /y/ 
-- 
-- Sets /res/ to the multiplicative inverse of /y/. Division by zero calls
-- /flint_abort/.
foreign import ccall "qqbar.h qqbar_inv"
  qqbar_inv :: Ptr CQQbar -> Ptr CQQbar -> Ptr CQQbar -> IO ()

-- | /qqbar_div/ /res/ /x/ /y/ 
-- 
-- Sets /res/ to the quotient of /x/ and /y/. Division by zero calls
-- /flint_abort/.
foreign import ccall "qqbar.h qqbar_div"
  qqbar_div :: Ptr CQQbar -> Ptr CQQbar -> Ptr CQQbar -> IO ()

-- | /qqbar_scalar_op/ /res/ /x/ /a/ /b/ /c/ 
-- 
-- Sets /res/ to the rational affine transformation \((ax+b)/c\), performed
-- as a single operation. There are no restrictions on /a/, /b/ and /c/
-- except that /c/ must be nonzero. Division by zero calls /flint_abort/.
foreign import ccall "qqbar.h qqbar_scalar_op"
  qqbar_scalar_op :: Ptr CQQbar -> Ptr CQQbar -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> IO ()

-- Powers and roots ------------------------------------------------------------

-- | /qqbar_sqrt/ /res/ /x/ 
-- 
-- Sets /res/ to the principal square root of /x/.
foreign import ccall "qqbar.h qqbar_sqrt"
  qqbar_sqrt :: Ptr CQQbar -> Ptr CQQbar -> IO ()

-- | /qqbar_rsqrt/ /res/ /x/ 
-- 
-- Sets /res/ to the reciprocal of the principal square root of /x/.
-- Division by zero calls /flint_abort/.
foreign import ccall "qqbar.h qqbar_rsqrt"
  qqbar_rsqrt :: Ptr CQQbar -> Ptr CQQbar -> IO ()

-- | /qqbar_pow_ui/ /res/ /x/ /n/ 
-- 
-- Sets /res/ to /x/ raised to the /n/-th power. Raising zero to a negative
-- power aborts.
foreign import ccall "qqbar.h qqbar_pow_ui"
  qqbar_pow_ui :: Ptr CQQbar -> Ptr CQQbar -> CULong -> IO ()

-- | /qqbar_root_ui/ /res/ /x/ /n/ 
-- 
-- Sets /res/ to the principal /n/-th root of /x/. The order /n/ must be
-- positive.
foreign import ccall "qqbar.h qqbar_root_ui"
  qqbar_root_ui :: Ptr CQQbar -> Ptr CQQbar -> CULong -> IO ()

-- | /qqbar_fmpq_pow_si_ui/ /res/ /x/ /m/ /n/ 
-- 
-- Sets /res/ to the principal branch of \(x^{m/n}\). The order /n/ must be
-- positive. Division by zero calls /flint_abort/.
foreign import ccall "qqbar.h qqbar_fmpq_pow_si_ui"
  qqbar_fmpq_pow_si_ui :: Ptr CQQbar -> Ptr CFmpq -> CLong -> CULong -> IO ()

-- | /qqbar_pow/ /res/ /x/ /y/ 
-- 
-- General exponentiation: if \(x^y\) is an algebraic number, sets /res/ to
-- this value and returns 1. If \(x^y\) is transcendental or undefined,
-- returns 0. Note that this function returns 0 instead of aborting on
-- division zero.
foreign import ccall "qqbar.h qqbar_pow"
  qqbar_pow :: Ptr CQQbar -> Ptr CQQbar -> Ptr CQQbar -> IO CInt

-- Numerical enclosures --------------------------------------------------------

-- The following functions guarantee a polished output in which both the
-- real and imaginary parts are accurate to /prec/ bits and exact when
-- exactly representable (that is, when a real or imaginary part is a
-- sufficiently small dyadic number). In some cases, the computations
-- needed to polish the output may be expensive. When polish is
-- unnecessary, @qqbar_enclosure_raw@ may be used instead. Alternatively,
-- @qqbar_cache_enclosure@ can be used to avoid recomputations.
--
-- | /qqbar_get_acb/ /res/ /x/ /prec/ 
-- 
-- Sets /res/ to an enclosure of /x/ rounded to /prec/ bits.
foreign import ccall "qqbar.h qqbar_get_acb"
  qqbar_get_acb :: Ptr CAcb -> Ptr CQQbar -> CLong -> IO ()

-- | /qqbar_get_arb/ /res/ /x/ /prec/ 
-- 
-- Sets /res/ to an enclosure of /x/ rounded to /prec/ bits, assuming that
-- /x/ is a real number. If /x/ is not real, /res/ is set to
-- \([\operatorname{NaN} \pm \infty]\).
foreign import ccall "qqbar.h qqbar_get_arb"
  qqbar_get_arb :: Ptr CArb -> Ptr CQQbar -> CLong -> IO ()

-- | /qqbar_get_arb_re/ /res/ /x/ /prec/ 
-- 
-- Sets /res/ to an enclosure of the real part of /x/ rounded to /prec/
-- bits.
foreign import ccall "qqbar.h qqbar_get_arb_re"
  qqbar_get_arb_re :: Ptr CArb -> Ptr CQQbar -> CLong -> IO ()

-- | /qqbar_get_arb_im/ /res/ /x/ /prec/ 
-- 
-- Sets /res/ to an enclosure of the imaginary part of /x/ rounded to
-- /prec/ bits.
foreign import ccall "qqbar.h qqbar_get_arb_im"
  qqbar_get_arb_im :: Ptr CArb -> Ptr CQQbar -> CLong -> IO ()

-- | /qqbar_cache_enclosure/ /res/ /prec/ 
-- 
-- Polishes the internal enclosure of /res/ to at least /prec/ bits of
-- precision in-place. Normally, /qqbar/ operations that need
-- high-precision enclosures compute them on the fly without caching the
-- results; if /res/ will be used as an invariant operand for many
-- operations, calling this function as a precomputation step can improve
-- performance.
foreign import ccall "qqbar.h qqbar_cache_enclosure"
  qqbar_cache_enclosure :: Ptr CQQbar -> CLong -> IO ()

-- Numerator and denominator ---------------------------------------------------

-- | /qqbar_denominator/ /res/ /y/ 
-- 
-- Sets /res/ to the denominator of /y/, i.e. the leading coefficient of
-- the minimal polynomial of /y/.
foreign import ccall "qqbar.h qqbar_denominator"
  qqbar_denominator :: Ptr CFmpz -> Ptr CQQbar -> IO ()

-- | /qqbar_numerator/ /res/ /y/ 
-- 
-- Sets /res/ to the numerator of /y/, i.e. /y/ multiplied by its
-- denominator.
foreign import ccall "qqbar.h qqbar_numerator"
  qqbar_numerator :: Ptr CQQbar -> Ptr CQQbar -> IO ()

-- Conjugates ------------------------------------------------------------------

-- | /qqbar_conjugates/ /res/ /x/ 
-- 
-- Sets the entries of the vector /res/ to the /d/ algebraic conjugates of
-- /x/, including /x/ itself, where /d/ is the degree of /x/. The output is
-- sorted in a canonical order (as defined by @qqbar_cmp_root_order@).
foreign import ccall "qqbar.h qqbar_conjugates"
  qqbar_conjugates :: Ptr CQQbar -> Ptr CQQbar -> IO ()

-- Polynomial evaluation -------------------------------------------------------

-- | /_qqbar_evaluate_fmpq_poly/ /res/ /poly/ /den/ /len/ /x/ 
-- 
-- Sets /res/ to the value of the given polynomial /poly/ evaluated at the
-- algebraic number /x/. These methods detect simple special cases and
-- automatically reduce /poly/ if its degree is greater or equal to that of
-- the minimal polynomial of /x/. In the generic case, evaluation is done
-- by computing minimal polynomials of representation matrices.
foreign import ccall "qqbar.h _qqbar_evaluate_fmpq_poly"
  _qqbar_evaluate_fmpq_poly :: Ptr CQQbar -> Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CQQbar -> IO ()

-- | /qqbar_evaluate_fmpz_mpoly_iter/ /res/ /poly/ /x/ /deg_limit/ /bits_limit/ /ctx/ 
-- 
-- Sets /res/ to the value of /poly/ evaluated at the algebraic numbers
-- given in the vector /x/. The number of variables is defined by the
-- context object /ctx/.
-- 
-- The parameters /deg_limit/ and /bits_limit/ define evaluation limits: if
-- any temporary result exceeds these limits (not necessarily the final
-- value, in case of cancellation), the evaluation is aborted and 0
-- (failure) is returned. If evaluation succeeds, 1 is returned.
-- 
-- The /iter/ version iterates over all terms in succession and computes
-- the powers that appear. The /horner/ version uses a multivariate
-- implementation of the Horner scheme. The default algorithm currently
-- uses the Horner scheme.
foreign import ccall "qqbar.h qqbar_evaluate_fmpz_mpoly_iter"
  qqbar_evaluate_fmpz_mpoly_iter :: Ptr CQQbar -> Ptr CFmpzMPoly -> Ptr CQQbar -> CLong -> CLong -> Ptr CFmpzMPolyCtx -> IO CInt

-- Polynomial roots ------------------------------------------------------------

-- | /qqbar_roots_fmpz_poly/ /res/ /poly/ /flags/ 
-- 
-- Sets the entries of the vector /res/ to the /d/ roots of the polynomial
-- /poly/. Roots with multiplicity appear with repetition in the output
-- array. By default, the roots will be sorted in a convenient canonical
-- order (as defined by @qqbar_cmp_root_order@). Instances of a repeated
-- root always appear consecutively.
-- 
-- The following /flags/ are supported:
-- 
-- -   QQBAR_ROOTS_IRREDUCIBLE - if set, /poly/ is assumed to be
--     irreducible (it may still have constant content), and no polynomial
--     factorization is performed internally.
-- -   QQBAR_ROOTS_UNSORTED - if set, the roots will not be guaranteed to
--     be sorted (except for repeated roots being listed consecutively).
foreign import ccall "qqbar.h qqbar_roots_fmpz_poly"
  qqbar_roots_fmpz_poly :: Ptr CQQbar -> Ptr CFmpzPoly -> CInt -> IO ()

-- | /qqbar_eigenvalues_fmpz_mat/ /res/ /mat/ /flags/ 
-- 
-- Sets the entries of the vector /res/ to the eigenvalues of the square
-- matrix /mat/. These functions compute the characteristic polynomial of
-- /mat/ and then call @qqbar_roots_fmpz_poly@ with the same flags.
foreign import ccall "qqbar.h qqbar_eigenvalues_fmpz_mat"
  qqbar_eigenvalues_fmpz_mat :: Ptr CQQbar -> Ptr CFmpzMat -> CInt -> IO ()

-- Roots of unity and trigonometric functions ----------------------------------

-- The following functions use word-size integers /p/ and /q/ instead of
-- /fmpq_t/ instances to express rational numbers. This is to emphasize
-- that the computations are feasible only with small /q/ in this
-- representation of algebraic numbers since the associated minimal
-- polynomials have degree \(O(q)\). The input /p/ and /q/ do not need to
-- be reduced /a priori/, but should not be close to the word boundaries
-- (they may be added and subtracted internally).
--
-- | /qqbar_root_of_unity/ /res/ /p/ /q/ 
-- 
-- Sets /res/ to the root of unity \(e^{2 \pi i p / q}\).
foreign import ccall "qqbar.h qqbar_root_of_unity"
  qqbar_root_of_unity :: Ptr CQQbar -> CLong -> CULong -> IO ()

-- | /qqbar_is_root_of_unity/ /p/ /q/ /x/ 
-- 
-- If /x/ is not a root of unity, returns 0. If /x/ is a root of unity,
-- returns 1. If /p/ and /q/ are not /NULL/ and /x/ is a root of unity,
-- this also sets /p/ and /q/ to the minimal integers with \(0 \le p < q\)
-- such that \(x = e^{2 \pi i p / q}\).
foreign import ccall "qqbar.h qqbar_is_root_of_unity"
  qqbar_is_root_of_unity :: Ptr CLong -> Ptr CULong -> Ptr CQQbar -> IO CInt

-- | /qqbar_exp_pi_i/ /res/ /p/ /q/ 
-- 
-- Sets /res/ to the root of unity \(e^{\pi i p / q}\).
foreign import ccall "qqbar.h qqbar_exp_pi_i"
  qqbar_exp_pi_i :: Ptr CQQbar -> CLong -> CULong -> IO ()

-- | /qqbar_cos_pi/ /res/ /p/ /q/ 
-- 
-- Sets /res/ to the trigonometric function \(\cos(\pi x)\),
-- \(\sin(\pi x)\), etc., with \(x = \tfrac{p}{q}\). The functions tan,
-- cot, sec and csc return the flag 1 if the value exists, and return 0 if
-- the evaluation point is a pole of the function.
foreign import ccall "qqbar.h qqbar_cos_pi"
  qqbar_cos_pi :: Ptr CQQbar -> CLong -> CULong -> IO ()

-- | /qqbar_log_pi_i/ /p/ /q/ /x/ 
-- 
-- If \(y = \operatorname{log}(x) / (\pi i)\) is algebraic, and hence
-- necessarily rational, sets \(y = p / q\) to the reduced such fraction
-- with \(-1 < y \le 1\) and returns 1. If /y/ is not algebraic, returns 0.
foreign import ccall "qqbar.h qqbar_log_pi_i"
  qqbar_log_pi_i :: Ptr CLong -> Ptr CULong -> Ptr CQQbar -> IO CInt

-- | /qqbar_atan_pi/ /p/ /q/ /x/ 
-- 
-- If \(y = \operatorname{atan}(x) / \pi\) is algebraic, and hence
-- necessarily rational, sets \(y = p / q\) to the reduced such fraction
-- with \(|y| < \tfrac{1}{2}\) and returns 1. If /y/ is not algebraic,
-- returns 0.
foreign import ccall "qqbar.h qqbar_atan_pi"
  qqbar_atan_pi :: Ptr CLong -> Ptr CULong -> Ptr CQQbar -> IO CInt

-- | /qqbar_asin_pi/ /p/ /q/ /x/ 
-- 
-- If \(y = \operatorname{asin}(x) / \pi\) is algebraic, and hence
-- necessarily rational, sets \(y = p / q\) to the reduced such fraction
-- with \(|y| \le \tfrac{1}{2}\) and returns 1. If /y/ is not algebraic,
-- returns 0.
foreign import ccall "qqbar.h qqbar_asin_pi"
  qqbar_asin_pi :: Ptr CLong -> Ptr CULong -> Ptr CQQbar -> IO CInt

-- | /qqbar_acos_pi/ /p/ /q/ /x/ 
-- 
-- If \(y = \operatorname{acos}(x) / \pi\) is algebraic, and hence
-- necessarily rational, sets \(y = p / q\) to the reduced such fraction
-- with \(0 \le y \le 1\) and returns 1. If /y/ is not algebraic, returns
-- 0.
foreign import ccall "qqbar.h qqbar_acos_pi"
  qqbar_acos_pi :: Ptr CLong -> Ptr CULong -> Ptr CQQbar -> IO CInt

-- | /qqbar_acot_pi/ /p/ /q/ /x/ 
-- 
-- If \(y = \operatorname{acot}(x) / \pi\) is algebraic, and hence
-- necessarily rational, sets \(y = p / q\) to the reduced such fraction
-- with \(-\tfrac{1}{2} < y \le \tfrac{1}{2}\) and returns 1. If /y/ is not
-- algebraic, returns 0.
foreign import ccall "qqbar.h qqbar_acot_pi"
  qqbar_acot_pi :: Ptr CLong -> Ptr CULong -> Ptr CQQbar -> IO CInt

-- | /qqbar_asec_pi/ /p/ /q/ /x/ 
-- 
-- If \(y = \operatorname{asec}(x) / \pi\) is algebraic, and hence
-- necessarily rational, sets \(y = p / q\) to the reduced such fraction
-- with \(0 \le y \le 1\) and returns 1. If /y/ is not algebraic, returns
-- 0.
foreign import ccall "qqbar.h qqbar_asec_pi"
  qqbar_asec_pi :: Ptr CLong -> Ptr CULong -> Ptr CQQbar -> IO CInt

-- | /qqbar_acsc_pi/ /p/ /q/ /x/ 
-- 
-- If \(y = \operatorname{acsc}(x) / \pi\) is algebraic, and hence
-- necessarily rational, sets \(y = p / q\) to the reduced such fraction
-- with \(-\tfrac{1}{2} \le y \le \tfrac{1}{2}\) and returns 1. If /y/ is
-- not algebraic, returns 0.
foreign import ccall "qqbar.h qqbar_acsc_pi"
  qqbar_acsc_pi :: Ptr CLong -> Ptr CULong -> Ptr CQQbar -> IO CInt

-- Guessing and simplification -------------------------------------------------

-- | /qqbar_guess/ /res/ /z/ /max_deg/ /max_bits/ /flags/ /prec/ 
-- 
-- Attempts to find an algebraic number /res/ of degree at most /max_deg/
-- and height at most /max_bits/ bits matching the numerical enclosure /z/.
-- The return flag indicates success. This is only a heuristic method, and
-- the return flag neither implies a rigorous proof that /res/ is the
-- correct result, nor a rigorous proof that no suitable algebraic number
-- with the given /max_deg/ and /max_bits/ exists. (Proof of nonexistence
-- could in principle be computed, but this is not yet implemented.)
-- 
-- The working precision /prec/ should normally be the same as the
-- precision used to compute /z/. It does not make much sense to run this
-- algorithm with precision smaller than O(/max_deg/ · /max_bits/).
-- 
-- This function does a single iteration at the target /max_deg/,
-- /max_bits/, and /prec/. For best performance, one should invoke this
-- function repeatedly with successively larger parameters when the size of
-- the intended solution is unknown or may be much smaller than a
-- worst-case bound.
foreign import ccall "qqbar.h qqbar_guess"
  qqbar_guess :: Ptr CQQbar -> Ptr CAcb -> CLong -> CLong -> CInt -> CLong -> IO CInt

-- | /qqbar_express_in_field/ /res/ /alpha/ /x/ /max_bits/ /flags/ /prec/ 
-- 
-- Attempts to express /x/ in the number field generated by /alpha/,
-- returning success (0 or 1). On success, /res/ is set to a polynomial /f/
-- of degree less than the degree of /alpha/ and with height (counting both
-- the numerator and the denominator, when the coefficients of /g/ are put
-- on a common denominator) bounded by /max_bits/ bits, such that
-- \(f(\alpha) = x\).
-- 
-- (Exception: the /max_bits/ parameter is currently ignored if /x/ is
-- rational, in which case /res/ is just set to the value of /x/.)
-- 
-- This function looks for a linear relation heuristically using a working
-- precision of /prec/ bits. If /x/ is expressible in terms of /alpha/,
-- then this function is guaranteed to succeed when /prec/ is taken large
-- enough. The identity \(f(\alpha) = x\) is checked rigorously, i.e. a
-- return value of 1 implies a proof of correctness. In principle, choosing
-- a sufficiently large /prec/ can be used to prove that /x/ does not lie
-- in the field generated by /alpha/, but the present implementation does
-- not support doing so automatically.
-- 
-- This function does a single iteration at the target /max_bits/ and and
-- /prec/. For best performance, one should invoke this function repeatedly
-- with successively larger parameters when the size of the intended
-- solution is unknown or may be much smaller than a worst-case bound.
foreign import ccall "qqbar.h qqbar_express_in_field"
  qqbar_express_in_field :: Ptr CFmpqPoly -> Ptr CQQbar -> Ptr CQQbar -> CLong -> CInt -> CLong -> IO CInt

-- Symbolic expressions and conversion to radicals -----------------------------

-- fexptr_t --------------------------------------------------------------------

data FExpr = FExpr {-# UNPACK #-} !(ForeignPtr CFExpr)
type CFExpr = CFlint FExpr

--------------------------------------------------------------------------------

-- | /qqbar_get_quadratic/ /a/ /b/ /c/ /q/ /x/ /factoring/ 
-- 
-- Assuming that /x/ has degree 1 or 2, computes integers /a/, /b/, /c/ and
-- /q/ such that
-- 
-- \[`\]
-- \[x = \frac{a + b \sqrt{c}}{q}\]
-- 
-- and such that /c/ is not a perfect square, /q/ is positive, and /q/ has
-- no content in common with both /a/ and /b/. In other words, this
-- determines a quadratic field \(\mathbb{Q}(\sqrt{c})\) containing /x/,
-- and then finds the canonical reduced coefficients /a/, /b/ and /q/
-- expressing /x/ in this field. For convenience, this function supports
-- rational /x/, for which /b/ and /c/ will both be set to zero. The
-- following remarks apply to irrationals.
-- 
-- The radicand /c/ will not be a perfect square, but will not
-- automatically be squarefree since this would require factoring the
-- discriminant. As a special case, /c/ will be set to \(-1\) if /x/ is a
-- Gaussian rational number. Otherwise, behavior is controlled by the
-- /factoring/ parameter.
-- 
-- -   If /factoring/ is 0, no factorization is performed apart from
--     removing powers of two.
-- -   If /factoring/ is 1, a complete factorization is performed (/c/ will
--     be minimal). This can be very expensive if the discriminant is
--     large.
-- -   If /factoring/ is 2, a smooth factorization is performed to remove
--     small factors from /c/. This is a tradeoff that provides pretty
--     output in most cases while avoiding extreme worst-case slowdown. The
--     smooth factorization guarantees finding all small factors (up to
--     some trial division limit determined internally by Flint), but large
--     factors are only found heuristically.
foreign import ccall "qqbar.h qqbar_get_quadratic"
  qqbar_get_quadratic :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> Ptr CQQbar -> CInt -> IO ()

-- | /qqbar_set_fexpr/ /res/ /expr/ 
-- 
-- Sets /res/ to the algebraic number represented by the symbolic
-- expression /expr/, returning 1 on success and 0 on failure.
-- 
-- This function performs a \"static\" evaluation using /qqbar/ arithmetic,
-- supporting only closed-form expressions with explicitly algebraic
-- subexpressions. It can be used to recover values generated by
-- @qqbar_get_expr_formula@ and variants. For evaluating more complex
-- expressions involving other types of values or requiring symbolic
-- simplifications, the user should preprocess /expr/ so that it is in a
-- form which can be parsed by @qqbar_set_fexpr@.
-- 
-- The following expressions are supported:
-- 
-- -   Integer constants
-- -   Arithmetic operations with algebraic operands
-- -   Square roots of algebraic numbers
-- -   Powers with algebraic base and exponent an explicit rational number
-- -   NumberI, GoldenRatio, RootOfUnity
-- -   Floor, Ceil, Abs, Sign, Csgn, Conjugate, Re, Im, Max, Min
-- -   Trigonometric functions with argument an explicit rational number
--     times Pi
-- -   Exponentials with argument an explicit rational number times Pi *
--     NumberI
-- -   The Decimal() constructor
-- -   AlgebraicNumberSerialized() (assuming valid data, which is not
--     checked)
-- -   PolynomialRootIndexed()
-- -   PolynomialRootNearest()
-- 
-- Examples of formulas that are not supported, despite the value being an
-- algebraic number:
-- 
-- -   @Pi - Pi@ (general transcendental simplifications are not performed)
-- -   @1 \/ Infinity@ (only numbers are handled)
-- -   @Sum(n, For(n, 1, 10))@ (only static evaluation is performed)
foreign import ccall "qqbar.h qqbar_set_fexpr"
  qqbar_set_fexpr :: Ptr CQQbar -> Ptr CFExpr -> IO CInt

-- | /qqbar_get_fexpr_repr/ /res/ /x/ 
-- 
-- Sets /res/ to a symbolic expression reflecting the exact internal
-- representation of /x/. The output will have the form
-- @AlgebraicNumberSerialized(List(coeffs), enclosure)@. The output can be
-- converted back to a @qqbar_t@ value using @qqbar_set_fexpr@. This is the
-- recommended format for serializing algebraic numbers as it requires
-- minimal computation, but it has the disadvantage of not being
-- human-readable.
foreign import ccall "qqbar.h qqbar_get_fexpr_repr"
  qqbar_get_fexpr_repr :: Ptr CFExpr -> Ptr CQQbar -> IO ()

-- | /qqbar_get_fexpr_root_nearest/ /res/ /x/ 
-- 
-- Sets /res/ to a symbolic expression unambiguously describing /x/ in the
-- form @PolynomialRootNearest(List(coeffs), point)@ where /point/ is an
-- approximation of /x/ guaranteed to be closer to /x/ than any conjugate
-- root. The output can be converted back to a @qqbar_t@ value using
-- @qqbar_set_fexpr@. This is a useful format for human-readable
-- presentation, but serialization and deserialization can be expensive.
foreign import ccall "qqbar.h qqbar_get_fexpr_root_nearest"
  qqbar_get_fexpr_root_nearest :: Ptr CFExpr -> Ptr CQQbar -> IO ()

-- | /qqbar_get_fexpr_root_indexed/ /res/ /x/ 
-- 
-- Sets /res/ to a symbolic expression unambiguously describing /x/ in the
-- form @PolynomialRootIndexed(List(coeffs), index)@ where /index/ is the
-- index of /x/ among its conjugate roots in the builtin root sort order.
-- The output can be converted back to a @qqbar_t@ value using
-- @qqbar_set_fexpr@. This is a useful format for human-readable
-- presentation when the numerical value is important, but serialization
-- and deserialization can be expensive.
foreign import ccall "qqbar.h qqbar_get_fexpr_root_indexed"
  qqbar_get_fexpr_root_indexed :: Ptr CFExpr -> Ptr CQQbar -> IO ()

-- | /qqbar_get_fexpr_formula/ /res/ /x/ /flags/ 
-- 
-- Attempts to express the algebraic number /x/ as a closed-form expression
-- using arithmetic operations, radicals, and possibly exponentials or
-- trigonometric functions, but without using @PolynomialRootNearest@ or
-- @PolynomialRootIndexed@. Returns 0 on failure and 1 on success.
-- 
-- The /flags/ parameter toggles different methods for generating formulas.
-- It can be set to any combination of the following. If /flags/ is 0, only
-- rational numbers will be handled.
-- 
-- QQBAR_FORMULA_ALL
-- 
-- Toggles all methods (potentially expensive).
-- 
-- QQBAR_FORMULA_GAUSSIANS
-- 
-- Detect Gaussian rational numbers \(a + bi\).
-- 
-- QQBAR_FORMULA_QUADRATICS
-- 
-- Solve quadratics in the form \(a + b \sqrt{d}\).
-- 
-- QQBAR_FORMULA_CYCLOTOMICS
-- 
-- Detect elements of cyclotomic fields. This works by trying plausible
-- cyclotomic fields (based on the degree of the input), using LLL to find
-- candidate number field elements, and certifying candidates through an
-- exact computation. Detection is heuristic and is not guaranteed to find
-- all cyclotomic numbers.
-- 
-- QQBAR_FORMULA_CUBICS QQBAR_FORMULA_QUARTICS QQBAR_FORMULA_QUINTICS
-- 
-- Solve polynomials of degree 3, 4 and (where applicable) 5 using cubic,
-- quartic and quintic formulas (not yet implemented).
-- 
-- QQBAR_FORMULA_DEPRESSION
-- 
-- Use depression to try to generate simpler numbers.
-- 
-- QQBAR_FORMULA_DEFLATION
-- 
-- Use deflation to try to generate simpler numbers. This allows handling
-- number of the form \(a^{1/n}\) where /a/ can be represented in closed
-- form.
-- 
-- QQBAR_FORMULA_SEPARATION
-- 
-- Try separating real and imaginary parts or sign and magnitude of complex
-- numbers. This allows handling numbers of the form \(a + bi\) or
-- \(m \cdot s\) (with \(m > 0, |s| = 1\)) where /a/ and /b/ or /m/ and /s/
-- can be represented in closed form. This is only attempted as a fallback
-- after other methods fail: if an explicit Cartesian or magnitude-sign
-- represented is desired, the user should manually separate the number
-- into complex parts before calling @qqbar_get_fexpr_formula@.
-- 
-- QQBAR_FORMULA_EXP_FORM QQBAR_FORMULA_TRIG_FORM
-- QQBAR_FORMULA_RADICAL_FORM QQBAR_FORMULA_AUTO_FORM
-- 
-- Select output form for cyclotomic numbers. The /auto/ form (equivalent
-- to no flags being set) results in radicals for numbers of low degree,
-- trigonometric functions for real numbers, and complex exponentials for
-- nonreal numbers. The other flags (not fully implemented) can be used to
-- force exponential form, trigonometric form, or radical form.
foreign import ccall "qqbar.h qqbar_get_fexpr_formula"
  qqbar_get_fexpr_formula :: Ptr CFExpr -> Ptr CQQbar -> CULong -> IO CInt

-- Internal functions ----------------------------------------------------------

-- | /qqbar_fmpz_poly_composed_op/ /res/ /A/ /B/ /op/ 
-- 
-- Given nonconstant polynomials /A/ and /B/, sets /res/ to a polynomial
-- whose roots are \(a+b\), \(a-b\), \(ab\) or \(a/b\) for all roots /a/ of
-- /A/ and all roots /b/ of /B/. The parameter /op/ selects the arithmetic
-- operation: 0 for addition, 1 for subtraction, 2 for multiplication and 3
-- for division. If /op/ is 3, /B/ must not have zero as a root.
foreign import ccall "qqbar.h qqbar_fmpz_poly_composed_op"
  qqbar_fmpz_poly_composed_op :: Ptr CFmpzPoly -> Ptr CFmpzPoly -> Ptr CFmpzPoly -> CInt -> IO ()

-- | /qqbar_binary_op/ /res/ /x/ /y/ /op/ 
-- 
-- Performs a binary operation using a generic algorithm. This does not
-- check for special cases.
foreign import ccall "qqbar.h qqbar_binary_op"
  qqbar_binary_op :: Ptr CQQbar -> Ptr CQQbar -> Ptr CQQbar -> CInt -> IO ()

-- | /_qqbar_validate_uniqueness/ /res/ /poly/ /z/ /max_prec/ 
-- 
-- Given /z/ known to be an enclosure of at least one root of /poly/,
-- certifies that the enclosure contains a unique root, and in that case
-- sets /res/ to a new (possibly improved) enclosure for the same root,
-- returning 1. Returns 0 if uniqueness cannot be certified.
-- 
-- The enclosure is validated by performing a single step with the interval
-- Newton method. The working precision is determined from the accuracy of
-- /z/, but limited by /max_prec/ bits.
-- 
-- This method slightly inflates the enclosure /z/ to improve the chances
-- that the interval Newton step will succeed. Uniqueness on this larger
-- interval implies uniqueness of the original interval, but not existence;
-- when existence has not been ensured a priori,
-- @_qqbar_validate_existence_uniqueness@ should be used instead.
foreign import ccall "qqbar.h _qqbar_validate_uniqueness"
  _qqbar_validate_uniqueness :: Ptr CAcb -> Ptr CFmpzPoly -> Ptr CAcb -> CLong -> IO CInt

-- | /_qqbar_validate_existence_uniqueness/ /res/ /poly/ /z/ /max_prec/ 
-- 
-- Given any complex interval /z/, certifies that the enclosure contains a
-- unique root of /poly/, and in that case sets /res/ to a new (possibly
-- improved) enclosure for the same root, returning 1. Returns 0 if
-- existence and uniqueness cannot be certified.
-- 
-- The enclosure is validated by performing a single step with the interval
-- Newton method. The working precision is determined from the accuracy of
-- /z/, but limited by /max_prec/ bits.
foreign import ccall "qqbar.h _qqbar_validate_existence_uniqueness"
  _qqbar_validate_existence_uniqueness :: Ptr CAcb -> Ptr CFmpzPoly -> Ptr CAcb -> CLong -> IO CInt

-- | /_qqbar_enclosure_raw/ /res/ /poly/ /z/ /prec/ 
-- 
-- Sets /res/ to an enclosure of /x/ accurate to about /prec/ bits (the
-- actual accuracy can be slightly lower, or higher).
-- 
-- This function uses repeated interval Newton steps to polish the initial
-- enclosure /z/, doubling the working precision each time. If any step
-- fails to improve the accuracy significantly, the root is recomputed from
-- scratch to higher precision.
-- 
-- If the initial enclosure is accurate enough, /res/ is set to this value
-- without rounding and without further computation.
foreign import ccall "qqbar.h _qqbar_enclosure_raw"
  _qqbar_enclosure_raw :: Ptr CAcb -> Ptr CFmpzPoly -> Ptr CAcb -> CLong -> IO ()

-- | /_qqbar_acb_lindep/ /rel/ /vec/ /len/ /check/ /prec/ 
-- 
-- Attempts to find an integer vector /rel/ giving a linear relation
-- between the elements of the real or complex vector /vec/, using the LLL
-- algorithm.
-- 
-- The working precision is set to the minimum of /prec/ and the relative
-- accuracy of /vec/ (that is, the difference between the largest magnitude
-- and the largest error magnitude within /vec/). 95% of the bits within
-- the working precision are used for the LLL matrix, and the remaining 5%
-- bits are used to validate the linear relation by evaluating the linear
-- combination and checking that the resulting interval contains zero. This
-- validation does not prove the existence or nonexistence of a linear
-- relation, but it provides a quick heuristic way to eliminate spurious
-- relations.
-- 
-- If /check/ is set, the return value indicates whether the validation was
-- successful; otherwise, the return value simply indicates whether the
-- algorithm was executed normally (failure may occur, for example, if the
-- input vector is non-finite).
-- 
-- In principle, this method can be used to produce a proof that no linear
-- relation exists with coefficients up to a specified bit size, but this
-- has not yet been implemented.
foreign import ccall "qqbar.h _qqbar_acb_lindep"
  _qqbar_acb_lindep :: Ptr CFmpz -> Ptr CAcb -> CLong -> CInt -> CLong -> IO CInt




