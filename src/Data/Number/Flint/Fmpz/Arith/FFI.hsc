{-# language
  CApiFFI
, FlexibleInstances
, ForeignFunctionInterface
, MultiParamTypeClasses
, TupleSections
, TypeFamilies
#-}

module Data.Number.Flint.Fmpz.Arith.FFI (
  -- * Arithmetic and special functions
  -- * Harmonic numbers
    _arith_harmonic_number
  -- * Stirling numbers
  , arith_stirling_number_1u
  , arith_stirling_number_1
  , arith_stirling_number_2
  , arith_stirling_number_1u_vec
  , arith_stirling_number_1_vec
  , arith_stirling_number_2_vec
  , arith_stirling_number_1u_vec_next
  , arith_stirling_number_1_vec_next
  , arith_stirling_number_2_vec_next
  , arith_stirling_matrix_1u
  , arith_stirling_matrix_1
  , arith_stirling_matrix_2
  -- * Bell numbers
  , arith_bell_number
  , arith_bell_number_vec
  , arith_bell_number_nmod
  , arith_bell_number_nmod_vec
  , arith_bell_number_size
  -- * Bernoulli numbers and polynomials
  , _arith_bernoulli_number
  , arith_bernoulli_number
  , _arith_bernoulli_number_vec
  , arith_bernoulli_number_vec
  , arith_bernoulli_number_denom
  , arith_bernoulli_number_size
  , arith_bernoulli_polynomial
  , _arith_bernoulli_number_zeta
  , _arith_bernoulli_number_vec_recursive
  , _arith_bernoulli_number_vec_zeta
  , _arith_bernoulli_number_vec_multi_mod
  -- * Euler numbers and polynomials
  , arith_euler_number
  , arith_euler_number_vec
  , arith_euler_number_size
  , arith_euler_polynomial
  , _arith_euler_number_zeta
  -- * Multiplicative functions
  , arith_divisors
  , arith_ramanujan_tau
  , arith_ramanujan_tau_series
  -- * Cyclotomic polynomials
  , _arith_cos_minpoly
  , arith_cos_minpoly
  -- * Landau\'s function
  , arith_landau_function_vec
  -- * Number of partitions
  , arith_number_of_partitions_vec
  , arith_number_of_partitions_nmod_vec
  , arith_hrr_expsum_factored
  , arith_number_of_partitions_mpfr
  , arith_number_of_partitions
  -- * Sums of squares
  , arith_sum_of_squares
  , arith_sum_of_squares_vec
) where 

-- arithmetic and special functions --------------------------------------------

import Foreign.C.String
import Foreign.C.Types
import Foreign.ForeignPtr
import Foreign.Ptr ( Ptr, FunPtr, plusPtr )
import Foreign.Storable
import Foreign.Marshal ( free )

import Data.Number.Flint.Flint
import Data.Number.Flint.Fmpz
import Data.Number.Flint.Fmpz.Poly
import Data.Number.Flint.Fmpz.Mat
import Data.Number.Flint.Fmpq
import Data.Number.Flint.Fmpq.Poly
import Data.Number.Flint.NMod

-- trig_prod_t -----------------------------------------------------------------

data FTrigProd = FTrigProd {-# UNPACK #-} !(ForeignPtr CFTrigProd) 
type CFTrigProd = CFlint FTrigProd

-- Harmonic numbers ------------------------------------------------------------

-- | /_arith_harmonic_number/ /num/ /den/ /n/ 
-- 
-- These are aliases for the functions in the fmpq module.
foreign import ccall "arith.h _arith_harmonic_number"
  _arith_harmonic_number :: Ptr CFmpz -> Ptr CFmpz -> CLong -> IO ()

-- Stirling numbers ------------------------------------------------------------

foreign import ccall "arith.h arith_stirling_number_1u"
  arith_stirling_number_1u :: Ptr CFmpz -> CULong -> CULong -> IO ()

foreign import ccall "arith.h arith_stirling_number_1"
  arith_stirling_number_1 :: Ptr CFmpz -> CULong -> CULong -> IO ()

-- | /arith_stirling_number_2/ /s/ /n/ /k/ 
-- 
-- Sets \(s\) to \(S(n,k)\) where \(S(n,k)\) denotes an unsigned Stirling
-- number of the first kind \(|S_1(n, k)|\), a signed Stirling number of
-- the first kind \(S_1(n, k)\), or a Stirling number of the second kind
-- \(S_2(n, k)\). The Stirling numbers are defined using the generating
-- functions
-- 
-- \[`\]
-- \[x_{(n)} = \sum_{k=0}^n S_1(n,k) x^k\]
-- \[x^{(n)} = \sum_{k=0}^n |S_1(n,k)| x^k\]
-- \[x^n     = \sum_{k=0}^n S_2(n,k) x_{(k)}\]
-- 
-- where \(x_{(n)} = x(x-1)(x-2) \dotsm (x-n+1)\) is a falling factorial
-- and \(x^{(n)} = x(x+1)(x+2) \dotsm (x+n-1)\) is a rising factorial.
-- \(S(n,k)\) is taken to be zero if \(n < 0\) or \(k < 0\).
-- 
-- These three functions are useful for computing isolated Stirling numbers
-- efficiently. To compute a range of numbers, the vector or matrix
-- versions should generally be used.
foreign import ccall "arith.h arith_stirling_number_2"
  arith_stirling_number_2 :: Ptr CFmpz -> CULong -> CULong -> IO ()

foreign import ccall "arith.h arith_stirling_number_1u_vec"
  arith_stirling_number_1u_vec :: Ptr CFmpz -> CULong -> CLong -> IO ()

foreign import ccall "arith.h arith_stirling_number_1_vec"
  arith_stirling_number_1_vec :: Ptr CFmpz -> CULong -> CLong -> IO ()

-- | /arith_stirling_number_2_vec/ /row/ /n/ /klen/ 
-- 
-- Computes the row of Stirling numbers
-- @S(n,0), S(n,1), S(n,2), ..., S(n,klen-1)@.
-- 
-- To compute a full row, this function can be called with @klen = n+1@. It
-- is assumed that @klen@ is at most \(n + 1\).
foreign import ccall "arith.h arith_stirling_number_2_vec"
  arith_stirling_number_2_vec :: Ptr CFmpz -> CULong -> CLong -> IO ()

foreign import ccall "arith.h arith_stirling_number_1u_vec_next"
  arith_stirling_number_1u_vec_next :: Ptr CFmpz -> Ptr CFmpz -> CLong -> CLong -> IO ()

foreign import ccall "arith.h arith_stirling_number_1_vec_next"
  arith_stirling_number_1_vec_next :: Ptr CFmpz -> Ptr CFmpz -> CLong -> CLong -> IO ()

-- | /arith_stirling_number_2_vec_next/ /row/ /prev/ /n/ /klen/ 
-- 
-- Given the vector @prev@ containing a row of Stirling numbers
-- @S(n-1,0), S(n-1,1), S(n-1,2), ..., S(n-1,klen-1)@, computes and stores
-- in the row argument @S(n,0), S(n,1), S(n,2), ..., S(n,klen-1)@.
-- 
-- If @klen@ is greater than @n@, the output ends with @S(n,n) = 1@
-- followed by @S(n,n+1) = S(n,n+2) = ... = 0@. In this case, the input
-- only needs to have length @n-1@; only the input entries up to
-- @S(n-1,n-2)@ are read.
-- 
-- The @row@ and @prev@ arguments are permitted to be the same, meaning
-- that the row will be updated in-place.
foreign import ccall "arith.h arith_stirling_number_2_vec_next"
  arith_stirling_number_2_vec_next :: Ptr CFmpz -> Ptr CFmpz -> CLong -> CLong -> IO ()

foreign import ccall "arith.h arith_stirling_matrix_1u"
  arith_stirling_matrix_1u :: Ptr CFmpzMat -> IO ()

foreign import ccall "arith.h arith_stirling_matrix_1"
  arith_stirling_matrix_1 :: Ptr CFmpzMat -> IO ()

-- | /arith_stirling_matrix_2/ /mat/ 
-- 
-- For an arbitrary \(m\)-by-n matrix, writes the truncation of the
-- infinite Stirling number matrix:
-- 
-- > row 0   : S(0,0)
-- > row 1   : S(1,0), S(1,1)
-- > row 2   : S(2,0), S(2,1), S(2,2)
-- > row 3   : S(3,0), S(3,1), S(3,2), S(3,3)
-- 
-- up to row \(m-1\) and column \(n-1\) inclusive. The upper triangular
-- part of the matrix is zeroed.
-- 
-- For any \(n\), the \(S_1\) and \(S_2\) matrices thus obtained are
-- inverses of each other.
foreign import ccall "arith.h arith_stirling_matrix_2"
  arith_stirling_matrix_2 :: Ptr CFmpzMat -> IO ()

-- Bell numbers ----------------------------------------------------------------

-- | /arith_bell_number/ /b/ /n/ 
-- 
-- Sets \(b\) to the Bell number \(B_n\), defined as the number of
-- partitions of a set with \(n\) members. Equivalently,
-- \(B_n = \sum_{k=0}^n S_2(n,k)\) where \(S_2(n,k)\) denotes a Stirling
-- number of the second kind.
-- 
-- The default version automatically selects between table lookup,
-- Dobinski\'s formula, and the multimodular algorithm.
-- 
-- The @dobinski@ version evaluates a precise truncation of the series
-- \(B_n = e^{-1} \sum_{k=0}^{\infty} \frac{k^n}{k!}\) (Dobinski\'s
-- formula). In fact, we compute \(P = N! \sum_{k=0}^N \frac{k^n}{k!}\) and
-- \(Q = N! \sum_{k=0}^N \frac{1}{k!} \approx N! e\) and evaluate
-- \(B_n = \lceil P / Q \rceil\), avoiding the use of floating-point
-- arithmetic.
-- 
-- The @multi_mod@ version computes the result modulo several limb-size
-- primes and reconstructs the integer value using the fast Chinese
-- remainder algorithm. A bound for the number of needed primes is computed
-- using @arith_bell_number_size@.
foreign import ccall "arith.h arith_bell_number"
  arith_bell_number :: Ptr CFmpz -> CULong -> IO ()

-- | /arith_bell_number_vec/ /b/ /n/ 
-- 
-- Sets \(b\) to the vector of Bell numbers \(B_0, B_1, \ldots, B_{n-1}\)
-- inclusive. The @recursive@ version uses the \(O(n^3 \log n)\) triangular
-- recurrence, while the @multi_mod@ version implements multimodular
-- evaluation of the exponential generating function, running in time
-- \(O(n^2 \log^{O(1)} n)\). The default version chooses an algorithm
-- automatically.
foreign import ccall "arith.h arith_bell_number_vec"
  arith_bell_number_vec :: Ptr CFmpz -> CLong -> IO ()

-- | /arith_bell_number_nmod/ /n/ /mod/ 
-- 
-- Computes the Bell number \(B_n\) modulo an integer given by @mod@.
-- 
-- After handling special cases, we use the formula
-- 
-- \[`\]
-- \[B_n = \sum_{k=0}^n \frac{(n-k)^n}{(n-k)!}
--     \sum_{j=0}^k \frac{(-1)^j}{j!}.\]
-- 
-- We arrange the operations in such a way that we only have to multiply
-- (and not divide) in the main loop. As a further optimisation, we use
-- sieving to reduce the number of powers that need to be evaluated. This
-- results in \(O(n)\) memory usage.
-- 
-- If the divisions by factorials are impossible, we fall back to calling
-- @arith_bell_number_nmod_vec@ and reading the last coefficient.
foreign import ccall "arith.h arith_bell_number_nmod"
  arith_bell_number_nmod :: CULong -> Ptr CNMod -> IO CMpLimb

-- | /arith_bell_number_nmod_vec/ /b/ /n/ /mod/ 
-- 
-- Sets \(b\) to the vector of Bell numbers \(B_0, B_1, \ldots, B_{n-1}\)
-- inclusive modulo an integer given by @mod@.
-- 
-- The /recursive/ version uses the \(O(n^2)\) triangular recurrence. The
-- /ogf/ version expands the ordinary generating function using binary
-- splitting, which is \(O(n \log^2 n)\).
-- 
-- The /series/ version uses the exponential generating function
-- \(\sum_{k=0}^{\infty} \frac{B_n}{n!} x^n = \exp(e^x-1)\), running in
-- \(O(n \log n)\). This only works if division by \(n!\) is possible, and
-- the function returns whether it is successful. All other versions
-- support any modulus.
-- 
-- The default version of this function selects an algorithm automatically.
foreign import ccall "arith.h arith_bell_number_nmod_vec"
  arith_bell_number_nmod_vec :: Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /arith_bell_number_size/ /n/ 
-- 
-- Returns \(b\) such that \(B_n < 2^{\lfloor b \rfloor}\). A previous
-- version of this function used the inequality
-- @B_n \< \\left(\\frac{0.792n}{\\log(n+1)}\\right)^n@ which is given in
-- < [BerTas2010]>; we now use a slightly better bound based on an
-- asymptotic expansion.
foreign import ccall "arith.h arith_bell_number_size"
  arith_bell_number_size :: CULong -> IO CDouble

-- Bernoulli numbers and polynomials -------------------------------------------

-- | /_arith_bernoulli_number/ /num/ /den/ /n/ 
-- 
-- Sets @(num, den)@ to the reduced numerator and denominator of the
-- \(n\)-th Bernoulli number. As presently implemented, this function
-- simply calls\\ @_arith_bernoulli_number_zeta@.
foreign import ccall "arith.h _arith_bernoulli_number"
  _arith_bernoulli_number :: Ptr CFmpz -> Ptr CFmpz -> CULong -> IO ()

-- | /arith_bernoulli_number/ /x/ /n/ 
-- 
-- Sets @x@ to the \(n\)-th Bernoulli number. This function is equivalent
-- to\\ @_arith_bernoulli_number@ apart from the output being a single
-- @fmpq_t@ variable.
-- 
-- Warning: this function does not use proven precision bounds, and could
-- return the wrong results for very large \(n\). It is recommended to use
-- the Bernoulli number functions in Arb instead.
foreign import ccall "arith.h arith_bernoulli_number"
  arith_bernoulli_number :: Ptr CFmpq -> CULong -> IO ()

-- | /_arith_bernoulli_number_vec/ /num/ /den/ /n/ 
-- 
-- Sets the elements of @num@ and @den@ to the reduced numerators and
-- denominators of the Bernoulli numbers \(B_0, B_1, B_2, \ldots, B_{n-1}\)
-- inclusive. This function automatically chooses between the @recursive@,
-- @zeta@ and @multi_mod@ algorithms according to the size of \(n\).
foreign import ccall "arith.h _arith_bernoulli_number_vec"
  _arith_bernoulli_number_vec :: Ptr CFmpz -> Ptr CFmpz -> CLong -> IO ()

-- | /arith_bernoulli_number_vec/ /x/ /n/ 
-- 
-- Sets the @x@ to the vector of Bernoulli numbers
-- \(B_0, B_1, B_2, \ldots, B_{n-1}\) inclusive. This function is
-- equivalent to @_arith_bernoulli_number_vec@ apart from the output being
-- a single @fmpq@ vector.
foreign import ccall "arith.h arith_bernoulli_number_vec"
  arith_bernoulli_number_vec :: Ptr CFmpq -> CLong -> IO ()

-- | /arith_bernoulli_number_denom/ /den/ /n/ 
-- 
-- Sets @den@ to the reduced denominator of the \(n\)-th Bernoulli number
-- \(B_n\). For even \(n\), the denominator is computed as the product of
-- all primes \(p\) for which \(p - 1\) divides \(n\); this property is a
-- consequence of the von Staudt-Clausen theorem. For odd \(n\), the
-- denominator is trivial (@den@ is set to 1 whenever \(B_n = 0\)). The
-- initial sequence of values smaller than \(2^{32}\) are looked up
-- directly from a table.
foreign import ccall "arith.h arith_bernoulli_number_denom"
  arith_bernoulli_number_denom :: Ptr CFmpz -> CULong -> IO ()

-- | /arith_bernoulli_number_size/ /n/ 
-- 
-- Returns \(b\) such that \(|B_n| < 2^{\lfloor b \rfloor}\), using the
-- inequality @|B_n| \< \\frac{4 n!}{(2\\pi)^n}@ and
-- \(n! \le (n+1)^{n+1} e^{-n}\). No special treatment is given to odd
-- \(n\). Accuracy is not guaranteed if \(n > 10^{14}\).
foreign import ccall "arith.h arith_bernoulli_number_size"
  arith_bernoulli_number_size :: CULong -> IO CDouble

-- | /arith_bernoulli_polynomial/ /poly/ /n/ 
-- 
-- Sets @poly@ to the Bernoulli polynomial of degree \(n\),
-- \(B_n(x) = \sum_{k=0}^n \binom{n}{k} B_k x^{n-k}\) where \(B_k\) is a
-- Bernoulli number. This function basically calls
-- @arith_bernoulli_number_vec@ and then rescales the coefficients
-- efficiently.
foreign import ccall "arith.h arith_bernoulli_polynomial"
  arith_bernoulli_polynomial :: Ptr CFmpqPoly -> CULong -> IO ()

-- | /_arith_bernoulli_number_zeta/ /num/ /den/ /n/ 
-- 
-- Sets @(num, den)@ to the reduced numerator and denominator of the
-- \(n\)-th Bernoulli number.
-- 
-- This function first computes the exact denominator and a bound for the
-- size of the numerator. It then computes an approximation of
-- \(|B_n| = 2n! \zeta(n) / (2 \pi)^n\) as a floating-point number and
-- multiplies by the denominator to to obtain a real number that rounds to
-- the exact numerator. For tiny \(n\), the numerator is looked up from a
-- table to avoid unnecessary overhead.
-- 
-- Warning: this function does not use proven precision bounds, and could
-- return the wrong results for very large \(n\). It is recommended to use
-- the Bernoulli number functions in Arb instead.
foreign import ccall "arith.h _arith_bernoulli_number_zeta"
  _arith_bernoulli_number_zeta :: Ptr CFmpz -> Ptr CFmpz -> CULong -> IO ()

-- | /_arith_bernoulli_number_vec_recursive/ /num/ /den/ /n/ 
-- 
-- Sets the elements of @num@ and @den@ to the reduced numerators and
-- denominators of \(B_0, B_1, B_2, \ldots, B_{n-1}\) inclusive.
-- 
-- The first few entries are computed using @arith_bernoulli_number@, and
-- then Ramanujan\'s recursive formula expressing \(B_m\) as a sum over
-- \(B_k\) for \(k\) congruent to \(m\) modulo 6 is applied repeatedly.
-- 
-- To avoid costly GCDs, the numerators are transformed internally to a
-- common denominator and all operations are performed using integer
-- arithmetic. This makes the algorithm fast for small \(n\), say
-- \(n < 1000\). The common denominator is calculated directly as the
-- primorial of \(n + 1\).
-- 
-- %[1] <https://en.wikipedia.org/w/index.php>? %
-- title=Bernoulli_number&oldid=405938876
foreign import ccall "arith.h _arith_bernoulli_number_vec_recursive"
  _arith_bernoulli_number_vec_recursive :: Ptr CFmpz -> Ptr CFmpz -> CLong -> IO ()

-- | /_arith_bernoulli_number_vec_zeta/ /num/ /den/ /n/ 
-- 
-- Sets the elements of @num@ and @den@ to the reduced numerators and
-- denominators of \(B_0, B_1, B_2, \ldots, B_{n-1}\) inclusive. Uses
-- repeated direct calls to\\ @_arith_bernoulli_number_zeta@.
foreign import ccall "arith.h _arith_bernoulli_number_vec_zeta"
  _arith_bernoulli_number_vec_zeta :: Ptr CFmpz -> Ptr CFmpz -> CLong -> IO ()

-- | /_arith_bernoulli_number_vec_multi_mod/ /num/ /den/ /n/ 
-- 
-- Sets the elements of @num@ and @den@ to the reduced numerators and
-- denominators of \(B_0, B_1, B_2, \ldots, B_{n-1}\) inclusive. Uses the
-- generating function
-- 
-- \[`\]
-- \[\frac{x^2}{\cosh(x)-1} = \sum_{k=0}^{\infty}
--     \frac{(2-4k) B_{2k}}{(2k)!} x^{2k}\]
-- 
-- which is evaluated modulo several limb-size primes using @nmod_poly@
-- arithmetic to yield the numerators of the Bernoulli numbers after
-- multiplication by the denominators and CRT reconstruction. This formula,
-- given (incorrectly) in < [BuhlerCrandallSompolski1992]>, saves about
-- half of the time compared to the usual generating function \(x/(e^x-1)\)
-- since the odd terms vanish.
foreign import ccall "arith.h _arith_bernoulli_number_vec_multi_mod"
  _arith_bernoulli_number_vec_multi_mod :: Ptr CFmpz -> Ptr CFmpz -> CLong -> IO ()

-- Euler numbers and polynomials -----------------------------------------------

-- Euler numbers are the integers \(E_n\) defined by frac{1}{cosh(t)} =
-- sum_{n=0}^{infty} frac{E_n}{n!} t^n. With this convention, the
-- odd-indexed numbers are zero and the even ones alternate signs, viz.
-- E_0, E_1, E_2, ldots = 1, 0, -1, 0, 5, 0, -61, 0, 1385, 0, ldots. The
-- corresponding Euler polynomials are defined by frac{2e^{xt}}{e^t+1} =
-- sum_{n=0}^{infty} frac{E_n(x)}{n!} t^n.
--
-- | /arith_euler_number/ /res/ /n/ 
-- 
-- Sets @res@ to the Euler number \(E_n\). Currently calls
-- @_arith_euler_number_zeta@.
-- 
-- Warning: this function does not use proven precision bounds, and could
-- return the wrong results for very large \(n\). It is recommended to use
-- the Euler number functions in Arb instead.
foreign import ccall "arith.h arith_euler_number"
  arith_euler_number :: Ptr CFmpz -> CULong -> IO ()

-- | /arith_euler_number_vec/ /res/ /n/ 
-- 
-- Computes the Euler numbers \(E_0, E_1, \dotsc, E_{n-1}\) for
-- \(n \geq 0\) and stores the result in @res@, which must be an
-- initialised @fmpz@ vector of sufficient size.
-- 
-- This function evaluates the even-index \(E_k\) modulo several limb-size
-- primes using the generating function and @nmod_poly@ arithmetic. A tight
-- bound for the number of needed primes is computed using
-- @arith_euler_number_size@, and the final integer values are recovered
-- using balanced CRT reconstruction.
foreign import ccall "arith.h arith_euler_number_vec"
  arith_euler_number_vec :: Ptr CFmpz -> CLong -> IO ()

-- | /arith_euler_number_size/ /n/ 
-- 
-- Returns \(b\) such that \(|E_n| < 2^{\lfloor b \rfloor}\), using the
-- inequality @|E_n| \< \\frac{2^{n+2} n!}{\\pi^{n+1}}@ and
-- \(n! \le (n+1)^{n+1} e^{-n}\). No special treatment is given to odd
-- \(n\). Accuracy is not guaranteed if \(n > 10^{14}\).
foreign import ccall "arith.h arith_euler_number_size"
  arith_euler_number_size :: CULong -> IO CDouble

-- | /arith_euler_polynomial/ /poly/ /n/ 
-- 
-- Sets @poly@ to the Euler polynomial \(E_n(x)\). Uses the formula
-- 
-- \[`\]
-- \[E_n(x) = \frac{2}{n+1}\left(B_{n+1}(x) - 
--     2^{n+1}B_{n+1}\left(\frac{x}{2}\right)\right),\]
-- 
-- with the Bernoulli polynomial \(B_{n+1}(x)\) evaluated once using
-- @bernoulli_polynomial@ and then rescaled.
foreign import ccall "arith.h arith_euler_polynomial"
  arith_euler_polynomial :: Ptr CFmpqPoly -> CULong -> IO ()

-- | /_arith_euler_number_zeta/ /res/ /n/ 
-- 
-- Sets @res@ to the Euler number \(E_n\). For even \(n\), this function
-- uses the relation @|E_n| = \\frac{2^{n+2} n!}{\\pi^{n+1}} L(n+1)@ where
-- \(L(n+1)\) denotes the Dirichlet \(L\)-function with character
-- \(\chi = \{ 0, 1, 0, -1 \}\).
-- 
-- Warning: this function does not use proven precision bounds, and could
-- return the wrong results for very large \(n\). It is recommended to use
-- the Euler number functions in Arb instead.
foreign import ccall "arith.h _arith_euler_number_zeta"
  _arith_euler_number_zeta :: Ptr CFmpz -> CULong -> IO ()

-- Multiplicative functions ----------------------------------------------------

-- | /arith_divisors/ /res/ /n/ 
-- 
-- Set the coefficients of the polynomial @res@ to the divisors of \(n\),
-- including \(1\) and \(n\) itself, in ascending order.
foreign import ccall "arith.h arith_divisors"
  arith_divisors :: Ptr CFmpzPoly -> Ptr CFmpz -> IO ()

-- | /arith_ramanujan_tau/ /res/ /n/ 
-- 
-- Sets @res@ to the Ramanujan tau function \(\tau(n)\) which is the
-- coefficient of \(q^n\) in the series expansion of
-- \(f(q) = q  \prod_{k \geq 1} \bigl(1 - q^k\bigr)^{24}\).
-- 
-- We factor \(n\) and use the identity \(\tau(pq) = \tau(p) \tau(q)\)
-- along with the recursion
-- \(\tau(p^{r+1}) = \tau(p) \tau(p^r) - p^{11} \tau(p^{r-1})\) for prime
-- powers.
-- 
-- The base values \(\tau(p)\) are obtained using the function
-- @arith_ramanujan_tau_series()@. Thus the speed of
-- @arith_ramanujan_tau()@ depends on the largest prime factor of \(n\).
-- 
-- Future improvement: optimise this function for small \(n\), which could
-- be accomplished using a lookup table or by calling
-- @arith_ramanujan_tau_series()@ directly.
foreign import ccall "arith.h arith_ramanujan_tau"
  arith_ramanujan_tau :: Ptr CFmpz -> Ptr CFmpz -> IO ()

-- | /arith_ramanujan_tau_series/ /res/ /n/ 
-- 
-- Sets @res@ to the polynomial with coefficients
-- \(\tau(0),\tau(1), \dotsc, \tau(n-1)\), giving the initial \(n\) terms
-- in the series expansion of
-- \(f(q) = q \prod_{k \geq 1} \bigl(1-q^k\bigr)^{24}\).
-- 
-- We use the theta function identity
-- 
-- \[`\]
-- \[f(q) = q  \Biggl( \sum_{k \geq 0} (-1)^k (2k+1) q^{k(k+1)/2} \Biggr)^8\]
-- 
-- which is evaluated using three squarings. The first squaring is done
-- directly since the polynomial is very sparse at this point.
foreign import ccall "arith.h arith_ramanujan_tau_series"
  arith_ramanujan_tau_series :: Ptr CFmpzPoly -> CLong -> IO ()

-- Cyclotomic polynomials ------------------------------------------------------

-- | /_arith_cos_minpoly/ /coeffs/ /d/ /n/ 
-- 
-- For \(n \ge 1\), sets @(coeffs, d+1)@ to the minimal polynomial
-- \(\Psi_n(x)\) of \(\cos(2 \pi / n)\), scaled to have integer
-- coefficients by multiplying by \(2^d\) (2^{d-1} when \(n\) is a power of
-- two).
-- 
-- The polynomial \(\Psi_n(x)\) is described in < [WaktinsZeitlin1993]>. As
-- proved in that paper, the roots of \(\Psi_n(x)\) for \(n \ge 3\) are
-- \(\cos(2 \pi k / n)\) where \(0 \le k < d\) and where
-- \(\gcd(k, n) = 1\).
-- 
-- To calculate \(\Psi_n(x)\), we compute the roots numerically with MPFR
-- and use a balanced product tree to form a polynomial with fixed-point
-- coefficients, i.e. an approximation of \(2^p 2^d \Psi_n(x)\).
-- 
-- To determine the precision \(p\), we note that the coefficients in
-- \(\prod_{i=1}^d (x - \alpha)\) can be bounded by the central coefficient
-- in the binomial expansion of \((x+1)^d\).
-- 
-- When \(n\) is an odd prime, we use a direct formula for the coefficients
-- (<https://mathworld.wolfram.com/TrigonometryAngles.html> ).
foreign import ccall "arith.h _arith_cos_minpoly"
  _arith_cos_minpoly :: Ptr CFmpz -> CLong -> CULong -> IO ()

-- | /arith_cos_minpoly/ /poly/ /n/ 
-- 
-- Sets @poly@ to the minimal polynomial \(\Psi_n(x)\) of
-- \(\cos(2 \pi / n)\), scaled to have integer coefficients. This
-- polynomial has degree 1 if \(n = 1\) or \(n = 2\), and degree
-- \(\phi(n) / 2\) otherwise.
-- 
-- We allow \(n = 0\) and define \(\Psi_0 = 1\).
foreign import ccall "arith.h arith_cos_minpoly"
  arith_cos_minpoly :: Ptr CFmpzPoly -> CULong -> IO ()

-- Landau\'s function ----------------------------------------------------------

-- | /arith_landau_function_vec/ /res/ /len/ 
-- 
-- Computes the first @len@ values of Landau\'s function \(g(n)\) starting
-- with \(g(0)\). Landau\'s function gives the largest order of an element
-- of the symmetric group \(S_n\).
-- 
-- Implements the \"basic algorithm\" given in
-- < [DelegliseNicolasZimmermann2009]>. The running time is
-- \(O(n^{3/2} / \sqrt{\log n})\).
foreign import ccall "arith.h arith_landau_function_vec"
  arith_landau_function_vec :: Ptr CFmpz -> CLong -> IO ()

-- Number of partitions --------------------------------------------------------

-- | /arith_number_of_partitions_vec/ /res/ /len/ 
-- 
-- Computes first @len@ values of the partition function \(p(n)\) starting
-- with \(p(0)\). Uses inversion of Euler\'s pentagonal series.
foreign import ccall "arith.h arith_number_of_partitions_vec"
  arith_number_of_partitions_vec :: Ptr CFmpz -> CLong -> IO ()

-- | /arith_number_of_partitions_nmod_vec/ /res/ /len/ /mod/ 
-- 
-- Computes first @len@ values of the partition function \(p(n)\) starting
-- with \(p(0)\), modulo the modulus defined by @mod@. Uses inversion of
-- Euler\'s pentagonal series.
foreign import ccall "arith.h arith_number_of_partitions_nmod_vec"
  arith_number_of_partitions_nmod_vec :: Ptr CMp -> CLong -> Ptr CNMod -> IO ()

-- | /arith_hrr_expsum_factored/ /prod/ /k/ /n/ 
-- 
-- Symbolically evaluates the exponential sum
-- 
-- \[`\]
-- \[A_k(n) = \sum_{h=0}^{k-1}
--     \exp\left(\pi i \left[ s(h,k) - \frac{2hn}{k}\right]\right)\]
-- 
-- appearing in the Hardy-Ramanujan-Rademacher formula, where \(s(h,k)\) is
-- a Dedekind sum.
-- 
-- Rather than evaluating the sum naively, we factor \(A_k(n)\) into a
-- product of cosines based on the prime factorisation of \(k\). This
-- process is based on the identities given in < [Whiteman1956]>.
-- 
-- The special @trig_prod_t@ structure @prod@ represents a product of
-- cosines of rational arguments, multiplied by an algebraic prefactor. It
-- must be pre-initialised with @trig_prod_init@.
-- 
-- This function assumes that \(24k\) and \(24n\) do not overflow a single
-- limb. If \(n\) is larger, it can be pre-reduced modulo \(k\), since
-- \(A_k(n)\) only depends on the value of \(n \bmod k\).
foreign import ccall "arith.h arith_hrr_expsum_factored"
  arith_hrr_expsum_factored :: Ptr CFTrigProd -> CMpLimb -> CMpLimb -> IO ()

-- | /arith_number_of_partitions_mpfr/ /x/ /n/ 
-- 
-- Sets the pre-initialised MPFR variable \(x\) to the exact value of
-- \(p(n)\). The value is computed using the Hardy-Ramanujan-Rademacher
-- formula.
-- 
-- The precision of \(x\) will be changed to allow \(p(n)\) to be
-- represented exactly. The interface of this function may be updated in
-- the future to allow computing an approximation of \(p(n)\) to smaller
-- precision.
-- 
-- The Hardy-Ramanujan-Rademacher formula is given with error bounds in
-- < [Rademacher1937]>. We evaluate it in the form
-- 
-- \[`\]
-- \[p(n) = \sum_{k=1}^N B_k(n) U(C/k) + R(n,N)\]
-- 
-- where
-- 
-- \[`\]
-- \[U(x) = \cosh(x) + \frac{\sinh(x)}{x},
--     \quad C = \frac{\pi}{6} \sqrt{24n-1}\]
-- \[B_k(n) = \sqrt{\frac{3}{k}} \frac{4}{24n-1} A_k(n)\]
-- 
-- and where \(A_k(n)\) is a certain exponential sum. The remainder
-- satisfies
-- 
-- \[`\]
-- \[|R(n,N)| < \frac{44 \pi^2}{225 \sqrt{3}} N^{-1/2} +
--     \frac{\pi \sqrt{2}}{75} \left(\frac{N}{n-1}\right)^{1/2}
--     \sinh\left(\pi \sqrt{\frac{2}{3}} \frac{\sqrt{n}}{N} \right).\]
-- 
-- We choose \(N\) such that \(|R(n,N)| < 0.25\), and a working precision
-- at term \(k\) such that the absolute error of the term is expected to be
-- less than \(0.25 / N\). We also use a summation variable with increased
-- precision, essentially making additions exact. Thus the sum of errors
-- adds up to less than 0.5, giving the correct value of \(p(n)\) when
-- rounding to the nearest integer.
-- 
-- The remainder estimate at step \(k\) provides an upper bound for the
-- size of the \(k\)-th term. We add \(\log_2 N\) bits to get low bits in
-- the terms below \(0.25 / N\) in magnitude.
-- 
-- Using @arith_hrr_expsum_factored@, each \(B_k(n)\) evaluation is broken
-- down to a product of cosines of exact rational multiples of \(\pi\). We
-- transform all angles to \((0, \pi/4)\) for optimal accuracy.
-- 
-- Since the evaluation of each term involves only \(O(\log k)\)
-- multiplications and evaluations of trigonometric functions of small
-- angles, the relative rounding error is at most a few bits. We therefore
-- just add an additional \(\log_2 (C/k)\) bits for the \(U(x)\) when \(x\)
-- is large. The cancellation of terms in \(U(x)\) is of no concern, since
-- Rademacher\'s bound allows us to terminate before \(x\) becomes small.
-- 
-- This analysis should be performed in more detail to give a rigorous
-- error bound, but the precision currently implemented is almost certainly
-- sufficient, not least considering that Rademacher\'s remainder bound
-- significantly overshoots the actual values.
-- 
-- To improve performance, we switch to doubles when the working precision
-- becomes small enough. We also use a separate accumulator variable which
-- gets added to the main sum periodically, in order to avoid costly
-- updates of the full-precision result when \(n\) is large.
foreign import ccall "arith.h arith_number_of_partitions_mpfr"
  arith_number_of_partitions_mpfr :: Ptr CMpfr -> CULong -> IO ()

-- | /arith_number_of_partitions/ /x/ /n/ 
-- 
-- Sets \(x\) to \(p(n)\), the number of ways that \(n\) can be written as
-- a sum of positive integers without regard to order.
-- 
-- This function uses a lookup table for \(n < 128\) (where
-- \(p(n) < 2^{32}\)), and otherwise calls
-- @arith_number_of_partitions_mpfr@.
foreign import ccall "arith.h arith_number_of_partitions"
  arith_number_of_partitions :: Ptr CFmpz -> CULong -> IO ()

-- Sums of squares -------------------------------------------------------------

-- | /arith_sum_of_squares/ /r/ /k/ /n/ 
-- 
-- Sets \(r\) to the number of ways \(r_k(n)\) in which \(n\) can be
-- represented as a sum of \(k\) squares.
-- 
-- If \(k = 2\) or \(k = 4\), we write \(r_k(n)\) as a divisor sum.
-- 
-- Otherwise, we either recurse on \(k\) or compute the theta function
-- expansion up to \(O(x^{n+1})\) and read off the last coefficient. This
-- is generally optimal.
foreign import ccall "arith.h arith_sum_of_squares"
  arith_sum_of_squares :: Ptr CFmpz -> CULong -> Ptr CFmpz -> IO ()

-- | /arith_sum_of_squares_vec/ /r/ /k/ /n/ 
-- 
-- For \(i = 0, 1, \ldots, n-1\), sets \(r_i\) to the number of
-- representations of \(i\) a sum of \(k\) squares, \(r_k(i)\). This
-- effectively computes the \(q\)-expansion of \(\vartheta_3(q)\) raised to
-- the \(k\)-th power, i.e.
-- 
-- \[`\]
-- \[\vartheta_3^k(q) = \left( \sum_{i=-\infty}^{\infty} q^{i^2} \right)^k.\]
foreign import ccall "arith.h arith_sum_of_squares_vec"
  arith_sum_of_squares_vec :: Ptr CFmpz -> CULong -> CLong -> IO ()
