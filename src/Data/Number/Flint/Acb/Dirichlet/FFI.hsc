{-# language
    CApiFFI
  , FlexibleInstances
  , ForeignFunctionInterface
  , MultiParamTypeClasses
  , TupleSections
  , TypeFamilies
  , ScopedTypeVariables
  #-}

module Data.Number.Flint.Acb.Dirichlet.FFI (
  -- * Dirichlet L-functions, Riemann zeta and related functions
  -- * Roots of unity
     DirichletRoots (..)
  , CDirichletRoots (..)
  , newDirichletRoots
  , withDirichletRoots
  , withNewDirichletRoots
  , acb_dirichlet_roots_init
  , acb_dirichlet_roots_clear
  , acb_dirichlet_root
  -- * Truncated L-series and power sums
  , acb_dirichlet_powsum_term
  , acb_dirichlet_powsum_sieved
  , acb_dirichlet_powsum_smooth
  -- * Riemann zeta function
  , acb_dirichlet_zeta
  , acb_dirichlet_zeta_jet
  , acb_dirichlet_zeta_bound
  , acb_dirichlet_zeta_deriv_bound
  , acb_dirichlet_eta
  , acb_dirichlet_xi
  -- * Riemann-Siegel formula
  , acb_dirichlet_zeta_rs_f_coeffs
  , acb_dirichlet_zeta_rs_d_coeffs
  , acb_dirichlet_zeta_rs_bound
  , acb_dirichlet_zeta_rs_r
  , acb_dirichlet_zeta_rs
  , acb_dirichlet_zeta_jet_rs
  -- * Hurwitz zeta function
  , acb_dirichlet_hurwitz
  -- * Hurwitz zeta function precomputation
  ,  DirichletHurwitzPrecomp (..)
  , CDirichletHurwitzPrecomp (..)
  , newDirichletHurwitzPrecomp
  , withDirichletHurwitzPrecomp
  , withNewDirichletHurwitzPrecomp
  , acb_dirichlet_hurwitz_precomp_init
  , acb_dirichlet_hurwitz_precomp_init_num
  , acb_dirichlet_hurwitz_precomp_clear
  , acb_dirichlet_hurwitz_precomp_choose_param
  , acb_dirichlet_hurwitz_precomp_bound
  , acb_dirichlet_hurwitz_precomp_eval
  -- * Lerch transcendent
  , acb_dirichlet_lerch_phi_integral
  -- * Stieltjes constants
  , acb_dirichlet_stieltjes
  -- * Dirichlet character evaluation
  , acb_dirichlet_chi
  , acb_dirichlet_chi_vec
  , acb_dirichlet_pairing
  , acb_dirichlet_pairing_char
  -- * Dirichlet character Gauss, Jacobi and theta sums
  , acb_dirichlet_gauss_sum_naive
  , acb_dirichlet_gauss_sum_factor
  , acb_dirichlet_gauss_sum_order2
  , acb_dirichlet_gauss_sum_theta
  , acb_dirichlet_gauss_sum
  , acb_dirichlet_gauss_sum_ui
  , acb_dirichlet_jacobi_sum_naive
  , acb_dirichlet_jacobi_sum_factor
  , acb_dirichlet_jacobi_sum_gauss
  , acb_dirichlet_jacobi_sum
  , acb_dirichlet_jacobi_sum_ui
  --, acb_dirichlet_chi_theta_arb
  , acb_dirichlet_ui_theta_arb
  , acb_dirichlet_theta_length
  , acb_dirichlet_qseries_powers_naive
  , acb_dirichlet_qseries_powers_smallorder
  -- * Discrete Fourier transforms
  , acb_dirichlet_dft_conrey
  , acb_dirichlet_dft
  -- * Dirichlet L-functions
  , acb_dirichlet_root_number_theta
  , acb_dirichlet_root_number
  , acb_dirichlet_l_hurwitz
  , acb_dirichlet_l_euler_product
  , _acb_dirichlet_euler_product_real_ui
  , acb_dirichlet_l
  , acb_dirichlet_l_fmpq
  , acb_dirichlet_l_vec_hurwitz
  , acb_dirichlet_l_jet
  , _acb_dirichlet_l_series
  , acb_dirichlet_l_series
  -- * Hardy Z-functions
  , acb_dirichlet_hardy_theta
  , acb_dirichlet_hardy_z
  , _acb_dirichlet_hardy_theta_series
  , acb_dirichlet_hardy_theta_series
  , _acb_dirichlet_hardy_z_series
  , acb_dirichlet_hardy_z_series
  -- * Gram points
  , acb_dirichlet_gram_point
  -- * Riemann zeta function zeros
  , acb_dirichlet_turing_method_bound
  , _acb_dirichlet_definite_hardy_z
  , _acb_dirichlet_isolate_gram_hardy_z_zero
  , _acb_dirichlet_isolate_rosser_hardy_z_zero
  , _acb_dirichlet_isolate_turing_hardy_z_zero
  , acb_dirichlet_isolate_hardy_z_zero
  , _acb_dirichlet_refine_hardy_z_zero
  , acb_dirichlet_hardy_z_zero
  , acb_dirichlet_hardy_z_zeros
  , acb_dirichlet_zeta_zero
  , acb_dirichlet_zeta_zeros
  , _acb_dirichlet_exact_zeta_nzeros
  , acb_dirichlet_zeta_nzeros
  , acb_dirichlet_backlund_s
  , acb_dirichlet_backlund_s_bound
  , acb_dirichlet_zeta_nzeros_gram
  , acb_dirichlet_backlund_s_gram
  -- * Riemann zeta function zeros (Platt\'s method)
  , acb_dirichlet_platt_scaled_lambda
  , acb_dirichlet_platt_scaled_lambda_vec
  , acb_dirichlet_platt_multieval
  , acb_dirichlet_platt_multieval_threaded
  , acb_dirichlet_platt_ws_interpolation
  , _acb_dirichlet_platt_local_hardy_z_zeros
  , acb_dirichlet_platt_local_hardy_z_zeros
  , acb_dirichlet_platt_hardy_z_zeros
  , acb_dirichlet_platt_zeta_zeros
) where 

-- Dirichlet L-functions, Riemann zeta and related functions

import Foreign.Ptr
import Foreign.ForeignPtr
import Foreign.C.Types
import Foreign.C.String
import Foreign.Storable

import Data.Number.Flint.Flint
import Data.Number.Flint.Fmpz
import Data.Number.Flint.Fmpq
import Data.Number.Flint.Groups.Dirichlet

import Data.Number.Flint.Arb.Types
import Data.Number.Flint.Acb.Types
import Data.Number.Flint.Acb.Poly

#include <flint/acb_dirichlet.h>

-- dirichlet_roots_t -----------------------------------------------------------

data DirichletRoots =
  DirichletRoots {-# UNPACK #-} !(ForeignPtr  CDirichletRoots)
type CDirichletRoots = CFlint DirichletRoots

instance Storable CDirichletRoots where
  sizeOf    _ = #{size      acb_dirichlet_roots_t}
  alignment _ = #{alignment acb_dirichlet_roots_t}
  peek = undefined
  poke = undefined

-- | Create new `DirichletRoots` /n/ /num/ /prec/
newDirichletRoots n num prec = do
  x <- mallocForeignPtr
  withForeignPtr x $ \x -> acb_dirichlet_roots_init x n num prec
  addForeignPtrFinalizer p_acb_dirichlet_roots_clear x
  return $ DirichletRoots x

-- | Use `DirichletRoots`
withDirichletRoots (DirichletRoots x) f = do
  withForeignPtr x $ \xp -> (DirichletRoots x,) <$> f xp

-- | Use new `DirichletRoots`
withNewDirichletRoots n num prec f = do
  x <- newDirichletRoots n num prec
  withDirichletRoots x f
  
-- acb_dirichlet_powers_t ------------------------------------------------------

data AcbDirichletPowers =
  AcbDirichletPowers {-# UNPACK #-} !(ForeignPtr  CAcbDirichletPowers)
type CAcbDirichletPowers = CFlint AcbDirichletPowers

-- Roots of unity --------------------------------------------------------------

-- | /acb_dirichlet_roots_init/ /roots/ /n/ /num/ /prec/ 
-- 
-- Initializes /roots/ with precomputed data for fast evaluation of roots
-- of unity \(e^{2\pi i k/n}\) of a fixed order /n/. The precomputation is
-- optimized for /num/ evaluations.
-- 
-- For very small /num/, only the single root \(e^{2\pi i/n}\) will be
-- precomputed, which can then be raised to a power. For small /prec/ and
-- large /n/, this method might even skip precomputing this single root if
-- it estimates that evaluating roots of unity from scratch will be faster
-- than powering.
-- 
-- If /num/ is large enough, the whole set of roots in the first quadrant
-- will be precomputed at once. However, this is automatically avoided for
-- large /n/ if too much memory would be used. For intermediate /num/,
-- baby-step giant-step tables are computed.
foreign import ccall "acb_dirichlet.h acb_dirichlet_roots_init"
  acb_dirichlet_roots_init :: Ptr CDirichletRoots -> CULong -> CLong -> CLong -> IO ()

-- | /acb_dirichlet_roots_clear/ /roots/ 
-- 
-- Clears the structure.
foreign import ccall "acb_dirichlet.h acb_dirichlet_roots_clear"
  acb_dirichlet_roots_clear :: Ptr CDirichletRoots -> IO ()

foreign import ccall "acb_dirichlet.h &acb_dirichlet_roots_clear"
  p_acb_dirichlet_roots_clear :: FunPtr (Ptr CDirichletRoots -> IO ())

-- | /acb_dirichlet_root/ /res/ /roots/ /k/ /prec/ 
-- 
-- Computes \(e^{2\pi i k/n}\).
foreign import ccall "acb_dirichlet.h acb_dirichlet_root"
  acb_dirichlet_root :: Ptr CAcb -> Ptr CDirichletRoots -> CULong -> CLong -> IO ()

-- Truncated L-series and power sums -------------------------------------------

-- | /acb_dirichlet_powsum_term/ /res/ /log_prev/ /prev/ /s/ /k/ /integer/ /critical_line/ /len/ /prec/ 
-- 
-- Sets /res/ to \(k^{-(s+x)}\) as a power series in /x/ truncated to
-- length /len/. The flags /integer/ and /critical_line/ respectively
-- specify optimizing for /s/ being an integer or having real part 1\/2.
-- 
-- On input /log_prev/ should contain the natural logarithm of the integer
-- at /prev/. If /prev/ is close to /k/, this can be used to speed up
-- computations. If \(\log(k)\) is computed internally by this function,
-- then /log_prev/ is overwritten by this value, and the integer at /prev/
-- is overwritten by /k/, allowing /log_prev/ to be recycled for the next
-- term when evaluating a power sum.
foreign import ccall "acb_dirichlet.h acb_dirichlet_powsum_term"
  acb_dirichlet_powsum_term :: Ptr CAcb -> Ptr CArb -> Ptr CULong -> Ptr CAcb -> CULong -> CInt -> CInt -> CLong -> CLong -> IO ()

-- | /acb_dirichlet_powsum_sieved/ /res/ /s/ /n/ /len/ /prec/ 
-- 
-- Sets /res/ to \(\sum_{k=1}^n k^{-(s+x)}\) as a power series in /x/
-- truncated to length /len/. This function stores a table of powers that
-- have already been calculated, computing \((ij)^r\) as \(i^r j^r\)
-- whenever \(k = ij\) is composite. As a further optimization, it groups
-- all even \(k\) and evaluates the sum as a polynomial in \(2^{-(s+x)}\).
-- This scheme requires about \(n / \log n\) powers, \(n / 2\)
-- multiplications, and temporary storage of \(n / 6\) power series. Due to
-- the extra power series multiplications, it is only faster than the naive
-- algorithm when /len/ is small.
foreign import ccall "acb_dirichlet.h acb_dirichlet_powsum_sieved"
  acb_dirichlet_powsum_sieved :: Ptr CAcb -> Ptr CAcb -> CULong -> CLong -> CLong -> IO ()

-- | /acb_dirichlet_powsum_smooth/ /res/ /s/ /n/ /len/ /prec/ 
-- 
-- Sets /res/ to \(\sum_{k=1}^n k^{-(s+x)}\) as a power series in /x/
-- truncated to length /len/. This function performs partial sieving by
-- adding multiples of 5-smooth /k/ into separate buckets. Asymptotically,
-- this requires computing 4\/15 of the powers, which is slower than
-- /sieved/, but only requires logarithmic extra space. It is also faster
-- for large /len/, since most power series multiplications are traded for
-- additions. A slightly bigger gain for larger /n/ could be achieved by
-- using more small prime factors, at the expense of space.
foreign import ccall "acb_dirichlet.h acb_dirichlet_powsum_smooth"
  acb_dirichlet_powsum_smooth :: Ptr CAcb -> Ptr CAcb -> CULong -> CLong -> CLong -> IO ()

-- Riemann zeta function -------------------------------------------------------

-- | /acb_dirichlet_zeta/ /res/ /s/ /prec/ 
-- 
-- Computes \(\zeta(s)\) using an automatic choice of algorithm.
foreign import ccall "acb_dirichlet.h acb_dirichlet_zeta"
  acb_dirichlet_zeta :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_dirichlet_zeta_jet/ /res/ /s/ /deflate/ /len/ /prec/ 
-- 
-- Computes the first /len/ terms of the Taylor series of the Riemann zeta
-- function at /s/. If /deflate/ is nonzero, computes the deflated function
-- \(\zeta(s) - 1/(s-1)\) instead.
foreign import ccall "acb_dirichlet.h acb_dirichlet_zeta_jet"
  acb_dirichlet_zeta_jet :: Ptr CAcb -> Ptr CAcb -> CInt -> CLong -> CLong -> IO ()

-- | /acb_dirichlet_zeta_bound/ /res/ /s/ 
-- 
-- Computes an upper bound for \(|\zeta(s)|\) quickly. On the critical
-- strip (and slightly outside of it), formula (43.3) in < [Rad1973]> is
-- used. To the right, evaluating at the real part of /s/ gives a trivial
-- bound. To the left, the functional equation is used.
foreign import ccall "acb_dirichlet.h acb_dirichlet_zeta_bound"
  acb_dirichlet_zeta_bound :: Ptr CMag -> Ptr CAcb -> IO ()

-- | /acb_dirichlet_zeta_deriv_bound/ /der1/ /der2/ /s/ 
-- 
-- Sets /der1/ to a bound for \(|\zeta'(s)|\) and /der2/ to a bound for
-- \(|\zeta''(s)|\). These bounds are mainly intended for use in the
-- critical strip and will not be tight.
foreign import ccall "acb_dirichlet.h acb_dirichlet_zeta_deriv_bound"
  acb_dirichlet_zeta_deriv_bound :: Ptr CMag -> Ptr CMag -> Ptr CAcb -> IO ()

-- | /acb_dirichlet_eta/ /res/ /s/ /prec/ 
-- 
-- Sets /res/ to the Dirichlet eta function
-- \(\eta(s) = \sum_{k=1}^{\infty} (-1)^{k+1} / k^s = (1-2^{1-s}) \zeta(s)\),
-- also known as the alternating zeta function. Note that the alternating
-- character \(\{1,-1\}\) is not itself a Dirichlet character.
foreign import ccall "acb_dirichlet.h acb_dirichlet_eta"
  acb_dirichlet_eta :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_dirichlet_xi/ /res/ /s/ /prec/ 
-- 
-- Sets /res/ to the Riemann xi function
-- \(\xi(s) = \frac{1}{2} s (s-1) \pi^{-s/2} \Gamma(\frac{1}{2} s) \zeta(s)\).
-- The functional equation for xi is \(\xi(1-s) = \xi(s)\).
foreign import ccall "acb_dirichlet.h acb_dirichlet_xi"
  acb_dirichlet_xi :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- Riemann-Siegel formula ------------------------------------------------------

-- The Riemann-Siegel (RS) formula is implemented closely following J.
-- Arias de Reyna < [Ari2011]>. For \(s = \sigma + it\) with \(t > 0\), the
-- expansion takes the form
--
-- \[`\]
-- \[\zeta(s) = \mathcal{R}(s) + X(s) \overline{\mathcal{R}}(1-s), \quad X(s) = \pi^{s-1/2} \frac{\Gamma((1-s)/2)}{\Gamma(s/2)}\]
--
-- where
--
-- \[`\]
-- \[\mathcal{R}(s) = \sum_{k=1}^N \frac{1}{k^s} + (-1)^{N-1} U a^{-\sigma} \left[ \sum_{k=0}^K \frac{C_k(p)}{a^k} + RS_K \right]\]
--
-- \[`\]
-- \[U = \exp\left(-i\left[ \frac{t}{2} \log\left(\frac{t}{2\pi}\right)-\frac{t}{2}-\frac{\pi}{8} \right]\right), \quad
-- a = \sqrt{\frac{t}{2\pi}}, \quad N = \lfloor a \rfloor, \quad p = 1-2(a-N).\]
--
-- The coefficients \(C_k(p)\) in the asymptotic part of the expansion are
-- expressed in terms of certain auxiliary coefficients \(d_j^{(k)}\) and
-- \(F^{(j)}(p)\). Because of artificial discontinuities, /s/ should be
-- exact inside the evaluation.
--
-- | /acb_dirichlet_zeta_rs_f_coeffs/ /f/ /p/ /n/ /prec/ 
-- 
-- Computes the coefficients \(F^{(j)}(p)\) for \(0 \le j < n\). Uses power
-- series division. This method breaks down when \(p = \pm 1/2\) (which is
-- not problem if /s/ is an exact floating-point number).
foreign import ccall "acb_dirichlet.h acb_dirichlet_zeta_rs_f_coeffs"
  acb_dirichlet_zeta_rs_f_coeffs :: Ptr CAcb -> Ptr CArb -> CLong -> CLong -> IO ()

-- | /acb_dirichlet_zeta_rs_d_coeffs/ /d/ /sigma/ /k/ /prec/ 
-- 
-- Computes the coefficients \(d_j^{(k)}\) for
-- \(0 \le j \le \lfloor 3k/2 \rfloor + 1\). On input, the array /d/ must
-- contain the coefficients for \(d_j^{(k-1)}\) unless \(k = 0\), and these
-- coefficients will be updated in-place.
foreign import ccall "acb_dirichlet.h acb_dirichlet_zeta_rs_d_coeffs"
  acb_dirichlet_zeta_rs_d_coeffs :: Ptr CArb -> Ptr CArb -> CLong -> CLong -> IO ()

-- | /acb_dirichlet_zeta_rs_bound/ /err/ /s/ /K/ 
-- 
-- Bounds the error term \(RS_K\) following Theorem 4.2 in Arias de Reyna.
foreign import ccall "acb_dirichlet.h acb_dirichlet_zeta_rs_bound"
  acb_dirichlet_zeta_rs_bound :: Ptr CMag -> Ptr CAcb -> CLong -> IO ()

-- | /acb_dirichlet_zeta_rs_r/ /res/ /s/ /K/ /prec/ 
-- 
-- Computes \(\mathcal{R}(s)\) in the upper half plane. Uses precisely /K/
-- asymptotic terms in the RS formula if this input parameter is positive;
-- otherwise chooses the number of terms automatically based on /s/ and the
-- precision.
foreign import ccall "acb_dirichlet.h acb_dirichlet_zeta_rs_r"
  acb_dirichlet_zeta_rs_r :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> IO ()

-- | /acb_dirichlet_zeta_rs/ /res/ /s/ /K/ /prec/ 
-- 
-- Computes \(\zeta(s)\) using the Riemann-Siegel formula. Uses precisely
-- /K/ asymptotic terms in the RS formula if this input parameter is
-- positive; otherwise chooses the number of terms automatically based on
-- /s/ and the precision.
foreign import ccall "acb_dirichlet.h acb_dirichlet_zeta_rs"
  acb_dirichlet_zeta_rs :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> IO ()

-- | /acb_dirichlet_zeta_jet_rs/ /res/ /s/ /len/ /prec/ 
-- 
-- Computes the first /len/ terms of the Taylor series of the Riemann zeta
-- function at /s/ using the Riemann Siegel formula. This function
-- currently only supports /len/ = 1 or /len/ = 2. A finite difference is
-- used to compute the first derivative.
foreign import ccall "acb_dirichlet.h acb_dirichlet_zeta_jet_rs"
  acb_dirichlet_zeta_jet_rs :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> IO ()

-- Hurwitz zeta function -------------------------------------------------------

-- | /acb_dirichlet_hurwitz/ /res/ /s/ /a/ /prec/ 
-- 
-- Computes the Hurwitz zeta function \(\zeta(s, a)\). This function
-- automatically delegates to the code for the Riemann zeta function when
-- \(a = 1\). Some other special cases may also be handled by direct
-- formulas. In general, Euler-Maclaurin summation is used.
foreign import ccall "acb_dirichlet.h acb_dirichlet_hurwitz"
  acb_dirichlet_hurwitz :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- Hurwitz zeta function precomputation ----------------------------------------

data DirichletHurwitzPrecomp = DirichletHurwitzPrecomp {-# UNPACK #-} !(ForeignPtr  CDirichletHurwitzPrecomp)
type  CDirichletHurwitzPrecomp = CFlint DirichletHurwitzPrecomp

instance Storable CDirichletHurwitzPrecomp where
  sizeOf _    = #{size      acb_dirichlet_hurwitz_precomp_t}
  alignment _ = #{alignment acb_dirichlet_hurwitz_precomp_t}
  peek = undefined
  poke = undefined

-- | Create new `DirichletHurwitzPrecomp`
newDirichletHurwitzPrecomp s deflate a k n prec = do
  x <- mallocForeignPtr
  withForeignPtr x $ \x -> do
    acb_dirichlet_hurwitz_precomp_init x s deflate a k n prec
  addForeignPtrFinalizer p_acb_dirichlet_hurwitz_precomp_clear x
  return $ DirichletHurwitzPrecomp x

-- | Use `f` on `DirichletHurwitzPrecomp`
withDirichletHurwitzPrecomp (DirichletHurwitzPrecomp x) f = do
  withForeignPtr x $ \xp -> (DirichletHurwitzPrecomp x,) <$> f xp

-- | Use `f` on new `DirichletHurwitzPrecomp`
withNewDirichletHurwitzPrecomp s deflate a k n prec f = do
  x <- newDirichletHurwitzPrecomp s deflate a k n prec
  withDirichletHurwitzPrecomp x f

--------------------------------------------------------------------------------

-- | /acb_dirichlet_hurwitz_precomp_init/ /pre/ /s/ /deflate/ /A/ /K/ /N/ /prec/ 
-- 
-- Precomputes a grid of Taylor polynomials for fast evaluation of
-- \(\zeta(s,a)\) on \(a \in (0,1]\) with fixed /s/. /A/ is the initial
-- shift to apply to /a/, /K/ is the number of Taylor terms, /N/ is the
-- number of grid points. The precomputation requires /NK/ evaluations of
-- the Hurwitz zeta function, and each subsequent evaluation requires /2K/
-- simple arithmetic operations (polynomial evaluation) plus /A/ powers. As
-- /K/ grows, the error is at most \(O(1/(2AN)^K)\).
-- 
-- This function can be called with /A/ set to zero, in which case no
-- Taylor series precomputation is performed. This means that evaluation
-- will be identical to calling @acb_dirichlet_hurwitz@ directly.
-- 
-- Otherwise, we require that /A/, /K/ and /N/ are all positive. For a
-- finite error bound, we require \(K+\operatorname{re}(s) > 1\). To avoid
-- an initial \"bump\" that steals precision and slows convergence, /AN/
-- should be at least roughly as large as \(|s|\), e.g. it is a good idea
-- to have at least \(AN > 0.5 |s|\).
-- 
-- If /deflate/ is set, the deflated Hurwitz zeta function is used,
-- removing the pole at \(s = 1\).
foreign import ccall "acb_dirichlet.h acb_dirichlet_hurwitz_precomp_init"
  acb_dirichlet_hurwitz_precomp_init :: Ptr CDirichletHurwitzPrecomp -> Ptr CAcb -> CInt -> CULong -> CULong -> CULong -> CLong -> IO ()

-- | /acb_dirichlet_hurwitz_precomp_init_num/ /pre/ /s/ /deflate/ /num_eval/ /prec/ 
-- 
-- Initializes /pre/, choosing the parameters /A/, /K/, and /N/
-- automatically to minimize the cost of /num_eval/ evaluations of the
-- Hurwitz zeta function at argument /s/ to precision /prec/.
foreign import ccall "acb_dirichlet.h acb_dirichlet_hurwitz_precomp_init_num"
  acb_dirichlet_hurwitz_precomp_init_num :: Ptr CDirichletHurwitzPrecomp -> Ptr CAcb -> CInt -> CDouble -> CLong -> IO ()

-- | /acb_dirichlet_hurwitz_precomp_clear/ /pre/ 
-- 
-- Clears the precomputed data.
foreign import ccall "acb_dirichlet.h acb_dirichlet_hurwitz_precomp_clear"
  acb_dirichlet_hurwitz_precomp_clear :: Ptr CDirichletHurwitzPrecomp -> IO ()

foreign import ccall "acb_dirichlet.h &acb_dirichlet_hurwitz_precomp_clear"
  p_acb_dirichlet_hurwitz_precomp_clear :: FunPtr (Ptr CDirichletHurwitzPrecomp -> IO ())

-- | /acb_dirichlet_hurwitz_precomp_choose_param/ /A/ /K/ /N/ /s/ /num_eval/ /prec/ 
-- 
-- Chooses precomputation parameters /A/, /K/ and /N/ to minimize the cost
-- of /num_eval/ evaluations of the Hurwitz zeta function at argument /s/
-- to precision /prec/. If it is estimated that evaluating each Hurwitz
-- zeta function from scratch would be better than performing a
-- precomputation, /A/, /K/ and /N/ are all set to 0.
foreign import ccall "acb_dirichlet.h acb_dirichlet_hurwitz_precomp_choose_param"
  acb_dirichlet_hurwitz_precomp_choose_param :: Ptr CULong -> Ptr CULong -> Ptr CULong -> Ptr CAcb -> CDouble -> CLong -> IO ()

-- | /acb_dirichlet_hurwitz_precomp_bound/ /res/ /s/ /A/ /K/ /N/ 
-- 
-- Computes an upper bound for the truncation error (not accounting for
-- roundoff error) when evaluating \(\zeta(s,a)\) with precomputation
-- parameters /A/, /K/, /N/, assuming that \(0 < a \le 1\). For details,
-- see @algorithms_hurwitz@.
foreign import ccall "acb_dirichlet.h acb_dirichlet_hurwitz_precomp_bound"
  acb_dirichlet_hurwitz_precomp_bound :: Ptr CMag -> Ptr CAcb -> CULong -> CULong -> CULong -> IO ()

-- | /acb_dirichlet_hurwitz_precomp_eval/ /res/ /pre/ /p/ /q/ /prec/ 
-- 
-- Evaluates \(\zeta(s,p/q)\) using precomputed data, assuming that
-- \(0 < p/q \le 1\).
foreign import ccall "acb_dirichlet.h acb_dirichlet_hurwitz_precomp_eval"
  acb_dirichlet_hurwitz_precomp_eval :: Ptr CAcb -> Ptr CDirichletHurwitzPrecomp -> CULong -> CULong -> CLong -> IO ()

-- Lerch transcendent ----------------------------------------------------------

-- | /acb_dirichlet_lerch_phi_integral/ /res/ /z/ /s/ /a/ /prec/ 
-- 
-- Computes the Lerch transcendent
-- 
-- \[`\]
-- \[\Phi(z,s,a) = \sum_{k=0}^{\infty} \frac{z^k}{(k+a)^s}\]
-- 
-- which is analytically continued for \(|z| \ge 1\).
-- 
-- The /direct/ version evaluates a truncation of the defining series. The
-- /integral/ version uses the Hankel contour integral
-- 
-- \[`\]
-- \[\Phi(z,s,a) = -\frac{\Gamma(1-s)}{2 \pi i} \int_C \frac{(-t)^{s-1} e^{-a t}}{1 - z e^{-t}} dt\]
-- 
-- where the path is deformed as needed to avoid poles and branch cuts of
-- the integrand. The default method chooses an algorithm automatically and
-- also checks for some special cases where the function can be expressed
-- in terms of simpler functions (Hurwitz zeta, polylogarithms).
foreign import ccall "acb_dirichlet.h acb_dirichlet_lerch_phi_integral"
  acb_dirichlet_lerch_phi_integral :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- Stieltjes constants ---------------------------------------------------------

-- | /acb_dirichlet_stieltjes/ /res/ /n/ /a/ /prec/ 
-- 
-- Given a nonnegative integer /n/, sets /res/ to the generalized Stieltjes
-- constant \(\gamma_n(a)\) which is the coefficient in the Laurent series
-- of the Hurwitz zeta function at the pole
-- 
-- \[`\]
-- \[\zeta(s,a) = \frac{1}{s-1} + \sum_{n=0}^\infty \frac{(-1)^n}{n!} \gamma_n(a) (s-1)^n.\]
-- 
-- With \(a = 1\), this gives the ordinary Stieltjes constants for the
-- Riemann zeta function.
-- 
-- This function uses an integral representation to permit fast computation
-- for extremely large /n/ < [JB2018]>. If /n/ is moderate and the
-- precision is high enough, it falls back to evaluating the Hurwitz zeta
-- function of a power series and reading off the last coefficient.
-- 
-- Note that for computing a range of values
-- \(\gamma_0(a), \ldots, \gamma_n(a)\), it is generally more efficient to
-- evaluate the Hurwitz zeta function series expansion once at \(s = 1\)
-- than to call this function repeatedly, unless /n/ is extremely large (at
-- least several hundred).
foreign import ccall "acb_dirichlet.h acb_dirichlet_stieltjes"
  acb_dirichlet_stieltjes :: Ptr CAcb -> Ptr CFmpz -> Ptr CAcb -> CLong -> IO ()

-- Dirichlet character evaluation ----------------------------------------------

-- | /acb_dirichlet_chi/ /res/ /G/ /chi/ /n/ /prec/ 
-- 
-- Sets /res/ to \(\chi(n)\), the value of the Dirichlet character /chi/ at
-- the integer /n/.
foreign import ccall "acb_dirichlet.h acb_dirichlet_chi"
  acb_dirichlet_chi :: Ptr CAcb -> Ptr CDirichletGroup -> Ptr CDirichletChar -> CULong -> CLong -> IO ()

-- | /acb_dirichlet_chi_vec/ /v/ /G/ /chi/ /nv/ /prec/ 
-- 
-- Compute the /nv/ first Dirichlet values.
foreign import ccall "acb_dirichlet.h acb_dirichlet_chi_vec"
  acb_dirichlet_chi_vec :: Ptr CAcb -> Ptr CDirichletGroup -> Ptr CDirichletChar -> CLong -> CLong -> IO ()

foreign import ccall "acb_dirichlet.h acb_dirichlet_pairing"
  acb_dirichlet_pairing :: Ptr CAcb -> Ptr CDirichletGroup -> CULong -> CULong -> CLong -> IO ()

-- | /acb_dirichlet_pairing_char/ /res/ /G/ /a/ /b/ /prec/ 
-- 
-- Sets /res/ to the value of the Dirichlet pairing \(\chi(m,n)\) at
-- numbers \(m\) and \(n\). The second form takes two characters as input.
foreign import ccall "acb_dirichlet.h acb_dirichlet_pairing_char"
  acb_dirichlet_pairing_char :: Ptr CAcb -> Ptr CDirichletGroup -> Ptr CDirichletChar -> Ptr CDirichletChar -> CLong -> IO ()

-- Dirichlet character Gauss, Jacobi and theta sums ----------------------------

foreign import ccall "acb_dirichlet.h acb_dirichlet_gauss_sum_naive"
  acb_dirichlet_gauss_sum_naive :: Ptr CAcb -> Ptr CDirichletGroup -> Ptr CDirichletChar -> CLong -> IO ()

foreign import ccall "acb_dirichlet.h acb_dirichlet_gauss_sum_factor"
  acb_dirichlet_gauss_sum_factor :: Ptr CAcb -> Ptr CDirichletGroup -> Ptr CDirichletChar -> CLong -> IO ()

foreign import ccall "acb_dirichlet.h acb_dirichlet_gauss_sum_order2"
  acb_dirichlet_gauss_sum_order2 :: Ptr CAcb -> Ptr CDirichletChar -> CLong -> IO ()

foreign import ccall "acb_dirichlet.h acb_dirichlet_gauss_sum_theta"
  acb_dirichlet_gauss_sum_theta :: Ptr CAcb -> Ptr CDirichletGroup -> Ptr CDirichletChar -> CLong -> IO ()

foreign import ccall "acb_dirichlet.h acb_dirichlet_gauss_sum"
  acb_dirichlet_gauss_sum :: Ptr CAcb -> Ptr CDirichletGroup -> Ptr CDirichletChar -> CLong -> IO ()

-- | /acb_dirichlet_gauss_sum_ui/ /res/ /G/ /a/ /prec/ 
-- 
-- Sets /res/ to the Gauss sum
-- 
-- \[G_q(a) = \sum_{x \bmod q} \chi_q(a, x) e^{\frac{2i\pi x}q}\]
-- 
-- -   the /naive/ version computes the sum as defined.
-- -   the /factor/ version writes it as a product of local Gauss sums by
--     chinese remainder theorem.
-- -   the /order2/ version assumes /chi/ is real and primitive and returns
--     \(i^p\sqrt q\) where \(p\) is the parity of \(\chi\).
-- -   the /theta/ version assumes that /chi/ is primitive to obtain the
--     Gauss sum by functional equation of the theta series at \(t=1\). An
--     abort will be raised if the theta series vanishes at \(t=1\). Only 4
--     exceptional characters of conductor 300 and 600 are known to have
--     this particularity, and none with primepower modulus.
-- -   the default version automatically combines the above methods.
-- -   the /ui/ version only takes the Conrey number /a/ as parameter.
foreign import ccall "acb_dirichlet.h acb_dirichlet_gauss_sum_ui"
  acb_dirichlet_gauss_sum_ui :: Ptr CAcb -> Ptr CDirichletGroup -> CULong -> CLong -> IO ()

foreign import ccall "acb_dirichlet.h acb_dirichlet_jacobi_sum_naive"
  acb_dirichlet_jacobi_sum_naive :: Ptr CAcb -> Ptr CDirichletGroup -> Ptr CDirichletChar -> Ptr CDirichletChar -> CLong -> IO ()

foreign import ccall "acb_dirichlet.h acb_dirichlet_jacobi_sum_factor"
  acb_dirichlet_jacobi_sum_factor :: Ptr CAcb -> Ptr CDirichletGroup -> Ptr CDirichletChar -> Ptr CDirichletChar -> CLong -> IO ()

foreign import ccall "acb_dirichlet.h acb_dirichlet_jacobi_sum_gauss"
  acb_dirichlet_jacobi_sum_gauss :: Ptr CAcb -> Ptr CDirichletGroup -> Ptr CDirichletChar -> Ptr CDirichletChar -> CLong -> IO ()

foreign import ccall "acb_dirichlet.h acb_dirichlet_jacobi_sum"
  acb_dirichlet_jacobi_sum :: Ptr CAcb -> Ptr CDirichletGroup -> Ptr CDirichletChar -> Ptr CDirichletChar -> CLong -> IO ()

-- | /acb_dirichlet_jacobi_sum_ui/ /res/ /G/ /a/ /b/ /prec/ 
-- 
-- Computes the Jacobi sum
-- 
-- \[J_q(a,b) = \sum_{x \bmod q} \chi_q(a, x)\chi_q(b, 1-x)\]
-- 
-- -   the /naive/ version computes the sum as defined.
-- -   the /factor/ version writes it as a product of local Jacobi sums
-- -   the /gauss/ version assumes \(ab\) is primitive and uses the formula
--     \(J_q(a,b)G_q(ab) = G_q(a)G_q(b)\)
-- -   the default version automatically combines the above methods.
-- -   the /ui/ version only takes the Conrey numbers /a/ and /b/ as
--     parameters.
foreign import ccall "acb_dirichlet.h acb_dirichlet_jacobi_sum_ui"
  acb_dirichlet_jacobi_sum_ui :: Ptr CAcb -> Ptr CDirichletGroup -> CULong -> CULong -> CLong -> IO ()

-- foreign import ccall "acb_dirichlet.h acb_dirichlet_chi_theta_arb"
--   acb_dirichlet_chi_theta_arb :: Ptr CAcb -> Ptr CDirichletGroup -> Ptr CDirichletChar -> Ptr CArb -> CLong -> IO ()

-- | /acb_dirichlet_ui_theta_arb/ /res/ /G/ /a/ /t/ /prec/ 
-- 
-- Compute the theta series \(\Theta_q(a,t)\) for real argument \(t>0\).
-- Beware that if \(t<1\) the functional equation
-- 
-- \[t \theta(a,t) = \epsilon(\chi) \theta\left(\frac1a, \frac1t\right)\]
-- 
-- should be used, which is not done automatically (to avoid recomputing
-- the Gauss sum).
-- 
-- We call /theta series/ of a Dirichlet character the quadratic series
-- 
-- \[\Theta_q(a) = \sum_{n\geq 0} \chi_q(a, n) n^p x^{n^2}\]
-- 
-- where \(p\) is the parity of the character \(\chi_q(a,\cdot)\).
-- 
-- For \(\Re(t)>0\) we write \(x(t)=\exp(-\frac{\pi}{N}t^2)\) and define
-- 
-- \[\Theta_q(a,t) = \sum_{n\geq 0} \chi_q(a, n) x(t)^{n^2}.\]
foreign import ccall "acb_dirichlet.h acb_dirichlet_ui_theta_arb"
  acb_dirichlet_ui_theta_arb :: Ptr CAcb -> Ptr CDirichletGroup -> CULong -> Ptr CArb -> CLong -> IO ()

-- | /acb_dirichlet_theta_length/ /q/ /t/ /prec/ 
-- 
-- Compute the number of terms to be summed in the theta series of argument
-- /t/ so that the tail is less than \(2^{-\mathrm{prec}}\).
foreign import ccall "acb_dirichlet.h acb_dirichlet_theta_length"
  acb_dirichlet_theta_length :: CULong -> Ptr CArb -> CLong -> IO CULong

foreign import ccall "acb_dirichlet.h acb_dirichlet_qseries_powers_naive"
  acb_dirichlet_qseries_powers_naive :: Ptr CAcb -> Ptr CArb -> CInt -> Ptr CULong -> Ptr CAcbDirichletPowers -> CLong -> CLong -> IO ()

-- | /acb_dirichlet_qseries_powers_smallorder/ /res/ /x/ /p/ /a/ /z/ /len/ /prec/ 
-- 
-- Compute the series \(\sum n^p z^{a_n} x^{n^2}\) for exponent list /a/,
-- precomputed powers /z/ and parity /p/ (being 0 or 1).
-- 
-- The /naive/ version sums the series as defined, while the /smallorder/
-- variant evaluates the series on the quotient ring by a cyclotomic
-- polynomial before evaluating at the root of unity, ignoring its argument
-- /z/.
foreign import ccall "acb_dirichlet.h acb_dirichlet_qseries_powers_smallorder"
  acb_dirichlet_qseries_powers_smallorder :: Ptr CAcb -> Ptr CArb -> CInt -> Ptr CULong -> Ptr CAcbDirichletPowers -> CLong -> CLong -> IO ()

-- Discrete Fourier transforms -------------------------------------------------

-- If \(f\) is a function \(\mathbb Z/q\mathbb Z\to \mathbb C\), its
-- discrete Fourier transform is the function defined on Dirichlet
-- characters mod \(q\) by
--
-- \[\hat f(\chi) = \sum_{x\mod q}\overline{\chi(x)}f(x)\]
--
-- See the @acb-dft@ module.
--
-- Here we take advantage of the Conrey isomorphism \(G \to \hat G\) to
-- consider the Fourier transform on Conrey labels as
--
-- \[g(a) = \sum_{b\bmod q}\overline{\chi_q(a,b)}f(b)\]
--
-- | /acb_dirichlet_dft_conrey/ /w/ /v/ /G/ /prec/ 
-- 
-- Compute the DFT of /v/ using Conrey indices. This function assumes /v/
-- and /w/ are vectors of size /G->phi_q/, whose values correspond to a
-- lexicographic ordering of Conrey logs (as obtained using
-- @dirichlet_char_next@ or by @dirichlet_char_index@).
-- 
-- For example, if \(q=15\), the Conrey elements are stored in following
-- order
-- 
-- > +-------+-------------+-------------------+
-- > | index | log = [e,f] | number = 7^e 11^f |
-- > +=======+=============+===================+
-- > | 0     | [0, 0]      | 1                 |
-- > +-------+-------------+-------------------+
-- > | 1     | [0, 1]      | 7                 |
-- > +-------+-------------+-------------------+
-- > | 2     | [0, 2]      | 4                 |
-- > +-------+-------------+-------------------+
-- > | 3     | [0, 3]      | 13                |
-- > +-------+-------------+-------------------+
-- > | 4     | [0, 4]      | 1                 |
-- > +-------+-------------+-------------------+
-- > | 5     | [1, 0]      | 11                |
-- > +-------+-------------+-------------------+
-- > | 6     | [1, 1]      | 2                 |
-- > +-------+-------------+-------------------+
-- > | 7     | [1, 2]      | 14                |
-- > +-------+-------------+-------------------+
-- > | 8     | [1, 3]      | 8                 |
-- > +-------+-------------+-------------------+
-- > | 9     | [1, 4]      | 11                |
-- > +-------+-------------+-------------------+
foreign import ccall "acb_dirichlet.h acb_dirichlet_dft_conrey"
  acb_dirichlet_dft_conrey :: Ptr CAcb -> Ptr CAcb -> Ptr CDirichletGroup -> CLong -> IO ()

-- | /acb_dirichlet_dft/ /w/ /v/ /G/ /prec/ 
-- 
-- Compute the DFT of /v/ using Conrey numbers. This function assumes /v/
-- and /w/ are vectors of size /G->q/. All values at index not coprime to
-- /G->q/ are ignored.
foreign import ccall "acb_dirichlet.h acb_dirichlet_dft"
  acb_dirichlet_dft :: Ptr CAcb -> Ptr CAcb -> Ptr CDirichletGroup -> CLong -> IO ()

-- Dirichlet L-functions -------------------------------------------------------

foreign import ccall "acb_dirichlet.h acb_dirichlet_root_number_theta"
  acb_dirichlet_root_number_theta :: Ptr CAcb -> Ptr CDirichletGroup -> Ptr CDirichletChar -> CLong -> IO ()

-- | /acb_dirichlet_root_number/ /res/ /G/ /chi/ /prec/ 
-- 
-- Sets /res/ to the root number \(\epsilon(\chi)\) for a primitive
-- character /chi/, which appears in the functional equation (where \(p\)
-- is the parity of \(\chi\)):
-- 
-- \[\left(\frac{q}{\pi}\right)^{\frac{s+p}2}\Gamma\left(\frac{s+p}2\right) L(s, \chi) = \epsilon(\chi) \left(\frac{q}{\pi}\right)^{\frac{1-s+p}2}\Gamma\left(\frac{1-s+p}2\right) L(1 - s, \overline\chi)\]
-- 
-- -   The /theta/ variant uses the evaluation at \(t=1\) of the Theta
--     series.
-- -   The default version computes it via the gauss sum.
foreign import ccall "acb_dirichlet.h acb_dirichlet_root_number"
  acb_dirichlet_root_number :: Ptr CAcb -> Ptr CDirichletGroup -> Ptr CDirichletChar -> CLong -> IO ()

-- | /acb_dirichlet_l_hurwitz/ /res/ /s/ /precomp/ /G/ /chi/ /prec/ 
-- 
-- Computes \(L(s,\chi)\) using decomposition in terms of the Hurwitz zeta
-- function
-- 
-- \[L(s,\chi) = q^{-s}\sum_{k=1}^q \chi(k) \,\zeta\!\left(s,\frac kq\right).\]
-- 
-- If \(s = 1\) and \(\chi\) is non-principal, the deflated Hurwitz zeta
-- function is used to avoid poles.
-- 
-- If /precomp/ is /NULL/, each Hurwitz zeta function value is computed
-- directly. If a pre-initialized /precomp/ object is provided, this will
-- be used instead to evaluate the Hurwitz zeta function.
foreign import ccall "acb_dirichlet.h acb_dirichlet_l_hurwitz"
  acb_dirichlet_l_hurwitz :: Ptr CAcb -> Ptr CAcb -> Ptr CDirichletHurwitzPrecomp -> Ptr CDirichletGroup -> Ptr CDirichletChar -> CLong -> IO ()

foreign import ccall "acb_dirichlet.h acb_dirichlet_l_euler_product"
  acb_dirichlet_l_euler_product :: Ptr CAcb -> Ptr CAcb -> Ptr CDirichletGroup -> Ptr CDirichletChar -> CLong -> IO ()

-- | /_acb_dirichlet_euler_product_real_ui/ /res/ /s/ /chi/ /mod/ /reciprocal/ /prec/ 
-- 
-- Computes \(L(s,\chi)\) directly using the Euler product. This is
-- efficient if /s/ has large positive real part. As implemented, this
-- function only gives a finite result if \(\operatorname{re}(s) \ge 2\).
-- 
-- An error bound is computed via @mag_hurwitz_zeta_uiui@. If /s/ is
-- complex, replace it with its real part. Since
-- 
-- \[`\]
-- \[\frac{1}{L(s,\chi)} = \prod_{p} \left(1 - \frac{\chi(p)}{p^s}\right)
--         = \sum_{k=1}^{\infty} \frac{\mu(k)\chi(k)}{k^s}\]
-- 
-- and the truncated product gives all smooth-index terms in the series, we
-- have
-- 
-- \[`\]
-- \[\left|\prod_{p < N} \left(1 - \frac{\chi(p)}{p^s}\right) - \frac{1}{L(s,\chi)}\right|
-- \le \sum_{k=N}^{\infty} \frac{1}{k^s} = \zeta(s,N).\]
-- 
-- The underscore version specialized for integer /s/ assumes that \(\chi\)
-- is a real Dirichlet character given by the explicit list /chi/ of
-- character values at 0, 1, ..., /mod/ - 1. If /reciprocal/ is set, it
-- computes \(1 / L(s,\chi)\) (this is faster if the reciprocal can be used
-- directly).
foreign import ccall "acb_dirichlet.h _acb_dirichlet_euler_product_real_ui"
  _acb_dirichlet_euler_product_real_ui :: Ptr CArb -> CULong -> CString -> CInt -> CInt -> CLong -> IO ()

-- | /acb_dirichlet_l/ /res/ /s/ /G/ /chi/ /prec/ 
-- 
-- Computes \(L(s,\chi)\) using a default choice of algorithm.
foreign import ccall "acb_dirichlet.h acb_dirichlet_l"
  acb_dirichlet_l :: Ptr CAcb -> Ptr CAcb -> Ptr CDirichletGroup -> Ptr CDirichletChar -> CLong -> IO ()

-- | /acb_dirichlet_l_fmpq/ /res/ /s/ /G/ /chi/ /prec/ 
-- 
-- Computes \(L(s,\chi)\) where /s/ is a rational number. The /afe/ version
-- uses the approximate functional equation; the default version chooses an
-- algorithm automatically.
foreign import ccall "acb_dirichlet.h acb_dirichlet_l_fmpq"
  acb_dirichlet_l_fmpq :: Ptr CAcb -> Ptr CFmpq -> Ptr CDirichletGroup -> Ptr CDirichletChar -> CLong -> IO ()

-- | /acb_dirichlet_l_vec_hurwitz/ /res/ /s/ /precomp/ /G/ /prec/ 
-- 
-- Compute all values \(L(s,\chi)\) for \(\chi\) mod \(q\), using the
-- Hurwitz zeta function and a discrete Fourier transform. The output /res/
-- is assumed to have length /G->phi_q/ and values are stored by
-- lexicographically ordered Conrey logs. See @acb_dirichlet_dft_conrey@.
-- 
-- If /precomp/ is /NULL/, each Hurwitz zeta function value is computed
-- directly. If a pre-initialized /precomp/ object is provided, this will
-- be used instead to evaluate the Hurwitz zeta function.
foreign import ccall "acb_dirichlet.h acb_dirichlet_l_vec_hurwitz"
  acb_dirichlet_l_vec_hurwitz :: Ptr CAcb -> Ptr CAcb -> Ptr CDirichletHurwitzPrecomp -> Ptr CDirichletGroup -> CLong -> IO ()

-- | /acb_dirichlet_l_jet/ /res/ /s/ /G/ /chi/ /deflate/ /len/ /prec/ 
-- 
-- Computes the Taylor expansion of \(L(s,\chi)\) to length /len/, i.e.
-- \(L(s), L'(s), \ldots, L^{(len-1)}(s) / (len-1)!\). If /deflate/ is set,
-- computes the expansion of
-- 
-- \[`\]
-- \[L(s,\chi) - \frac{\sum_{k=1}^q \chi(k)}{(s-1)q}\]
-- 
-- instead. If /chi/ is a principal character, then this has the effect of
-- subtracting the pole with residue \(\sum_{k=1}^q \chi(k) = \phi(q) / q\)
-- that is located at \(s = 1\). In particular, when evaluated at
-- \(s = 1\), this gives the regular part of the Laurent expansion. When
-- /chi/ is non-principal, /deflate/ has no effect.
foreign import ccall "acb_dirichlet.h acb_dirichlet_l_jet"
  acb_dirichlet_l_jet :: Ptr CAcb -> Ptr CAcb -> Ptr CDirichletGroup -> Ptr CDirichletChar -> CInt -> CLong -> CLong -> IO ()

foreign import ccall "acb_dirichlet.h _acb_dirichlet_l_series"
  _acb_dirichlet_l_series :: Ptr CAcb -> Ptr CAcb -> CLong -> Ptr CDirichletGroup -> Ptr CDirichletChar -> CInt -> CLong -> CLong -> IO ()

-- | /acb_dirichlet_l_series/ /res/ /s/ /G/ /chi/ /deflate/ /len/ /prec/ 
-- 
-- Sets /res/ to the power series \(L(s,\chi)\) where /s/ is a given power
-- series, truncating the result to length /len/. See @acb_dirichlet_l_jet@
-- for the meaning of the /deflate/ flag.
foreign import ccall "acb_dirichlet.h acb_dirichlet_l_series"
  acb_dirichlet_l_series :: Ptr CAcbPoly -> Ptr CAcbPoly -> Ptr CDirichletGroup -> Ptr CDirichletChar -> CInt -> CLong -> CLong -> IO ()

-- Hardy Z-functions -----------------------------------------------------------

-- For convenience, setting both /G/ and /chi/ to /NULL/ in the following
-- methods selects the Riemann zeta function.
--
-- Currently, these methods require /chi/ to be a primitive character.
--
-- | /acb_dirichlet_hardy_theta/ /res/ /t/ /G/ /chi/ /len/ /prec/ 
-- 
-- Computes the phase function used to construct the Z-function. We have
-- 
-- \[`\]
-- \[\theta(t) = -\frac{t}{2} \log(\pi/q) - \frac{i \log(\epsilon)}{2}
--     + \frac{\log \Gamma((s+\delta)/2) - \log \Gamma((1-s+\delta)/2)}{2i}\]
-- 
-- where \(s = 1/2+it\), \(\delta\) is the parity of /chi/, and
-- \(\epsilon\) is the root number as computed by
-- @acb_dirichlet_root_number@. The first /len/ terms in the Taylor
-- expansion are written to the output.
foreign import ccall "acb_dirichlet.h acb_dirichlet_hardy_theta"
  acb_dirichlet_hardy_theta :: Ptr CAcb -> Ptr CAcb -> Ptr CDirichletGroup -> Ptr CDirichletChar -> CLong -> CLong -> IO ()

-- | /acb_dirichlet_hardy_z/ /res/ /t/ /G/ /chi/ /len/ /prec/ 
-- 
-- Computes the Hardy Z-function, also known as the Riemann-Siegel
-- Z-function \(Z(t) = e^{i \theta(t)} L(1/2+it)\), which is real-valued
-- for real /t/. The first /len/ terms in the Taylor expansion are written
-- to the output.
foreign import ccall "acb_dirichlet.h acb_dirichlet_hardy_z"
  acb_dirichlet_hardy_z :: Ptr CAcb -> Ptr CAcb -> Ptr CDirichletGroup -> Ptr CDirichletChar -> CLong -> CLong -> IO ()

foreign import ccall "acb_dirichlet.h _acb_dirichlet_hardy_theta_series"
  _acb_dirichlet_hardy_theta_series :: Ptr CAcb -> Ptr CAcb -> CLong -> Ptr CDirichletGroup -> Ptr CDirichletChar -> CLong -> CLong -> IO ()

-- | /acb_dirichlet_hardy_theta_series/ /res/ /t/ /G/ /chi/ /len/ /prec/ 
-- 
-- Sets /res/ to the power series \(\theta(t)\) where /t/ is a given power
-- series, truncating the result to length /len/.
foreign import ccall "acb_dirichlet.h acb_dirichlet_hardy_theta_series"
  acb_dirichlet_hardy_theta_series :: Ptr CAcbPoly -> Ptr CAcbPoly -> Ptr CDirichletGroup -> Ptr CDirichletChar -> CLong -> CLong -> IO ()

foreign import ccall "acb_dirichlet.h _acb_dirichlet_hardy_z_series"
  _acb_dirichlet_hardy_z_series :: Ptr CAcb -> Ptr CAcb -> CLong -> Ptr CDirichletGroup -> Ptr CDirichletChar -> CLong -> CLong -> IO ()

-- | /acb_dirichlet_hardy_z_series/ /res/ /t/ /G/ /chi/ /len/ /prec/ 
-- 
-- Sets /res/ to the power series \(Z(t)\) where /t/ is a given power
-- series, truncating the result to length /len/.
foreign import ccall "acb_dirichlet.h acb_dirichlet_hardy_z_series"
  acb_dirichlet_hardy_z_series :: Ptr CAcbPoly -> Ptr CAcbPoly -> Ptr CDirichletGroup -> Ptr CDirichletChar -> CLong -> CLong -> IO ()

-- Gram points -----------------------------------------------------------------

-- | /acb_dirichlet_gram_point/ /res/ /n/ /G/ /chi/ /prec/ 
-- 
-- Sets /res/ to the /n/-th Gram point \(g_n\), defined as the unique
-- solution in \([7, \infty)\) of \(\theta(g_n) = \pi n\). Currently only
-- the Gram points corresponding to the Riemann zeta function are supported
-- and /G/ and /chi/ must both be set to /NULL/. Requires \(n \ge -1\).
foreign import ccall "acb_dirichlet.h acb_dirichlet_gram_point"
  acb_dirichlet_gram_point :: Ptr CArb -> Ptr CFmpz -> Ptr CDirichletGroup -> Ptr CDirichletChar -> CLong -> IO ()

-- Riemann zeta function zeros -------------------------------------------------

-- The following functions for counting and isolating zeros of the Riemann
-- zeta function use the ideas from the implementation of Turing\'s method
-- in mpmath < [Joh2018b]> by Juan Arias de Reyna, described in
-- < [Ari2012]>.
--
-- | /acb_dirichlet_turing_method_bound/ /p/ 
-- 
-- Computes an upper bound /B/ for the minimum number of consecutive good
-- Gram blocks sufficient to count nontrivial zeros of the Riemann zeta
-- function using Turing\'s method < [Tur1953]> as updated by < [Leh1970]>,
-- < [Bre1979]>, and < [Tru2011]>.
-- 
-- Let \(N(T)\) denote the number of zeros (counted according to their
-- multiplicities) of \(\zeta(s)\) in the region
-- \(0 < \operatorname{Im}(s) \le T\). If at least /B/ consecutive Gram
-- blocks with union \([g_n, g_p)\) satisfy Rosser\'s rule, then
-- \(N(g_n) \le n + 1\) and \(N(g_p) \ge p + 1\).
foreign import ccall "acb_dirichlet.h acb_dirichlet_turing_method_bound"
  acb_dirichlet_turing_method_bound :: Ptr CFmpz -> IO CULong

-- | /_acb_dirichlet_definite_hardy_z/ /res/ /t/ /pprec/ 
-- 
-- Sets /res/ to the Hardy Z-function \(Z(t)\). The initial precision (*
-- /pprec/) is increased as necessary to determine the sign of \(Z(t)\).
-- The sign is returned.
foreign import ccall "acb_dirichlet.h _acb_dirichlet_definite_hardy_z"
  _acb_dirichlet_definite_hardy_z :: Ptr CArb -> Ptr CArf -> Ptr CLong -> IO CInt

-- | /_acb_dirichlet_isolate_gram_hardy_z_zero/ /a/ /b/ /n/ 
-- 
-- Uses Gram\'s law to compute an interval \((a, b)\) that contains the
-- /n/-th zero of the Hardy Z-function and no other zero. Requires
-- \(1 \le n \le 126\).
foreign import ccall "acb_dirichlet.h _acb_dirichlet_isolate_gram_hardy_z_zero"
  _acb_dirichlet_isolate_gram_hardy_z_zero :: Ptr CArf -> Ptr CArf -> Ptr CFmpz -> IO ()

-- | /_acb_dirichlet_isolate_rosser_hardy_z_zero/ /a/ /b/ /n/ 
-- 
-- Uses Rosser\'s rule to compute an interval \((a, b)\) that contains the
-- /n/-th zero of the Hardy Z-function and no other zero. Requires
-- \(1 \le n \le 13999526\).
foreign import ccall "acb_dirichlet.h _acb_dirichlet_isolate_rosser_hardy_z_zero"
  _acb_dirichlet_isolate_rosser_hardy_z_zero :: Ptr CArf -> Ptr CArf -> Ptr CFmpz -> IO ()

-- | /_acb_dirichlet_isolate_turing_hardy_z_zero/ /a/ /b/ /n/ 
-- 
-- Computes an interval \((a, b)\) that contains the /n/-th zero of the
-- Hardy Z-function and no other zero, following Turing\'s method. Requires
-- \(n \ge 2\).
foreign import ccall "acb_dirichlet.h _acb_dirichlet_isolate_turing_hardy_z_zero"
  _acb_dirichlet_isolate_turing_hardy_z_zero :: Ptr CArf -> Ptr CArf -> Ptr CFmpz -> IO ()

-- | /acb_dirichlet_isolate_hardy_z_zero/ /a/ /b/ /n/ 
-- 
-- Computes an interval \((a, b)\) that contains the /n/-th zero of the
-- Hardy Z-function and contains no other zero, using the most appropriate
-- underscore version of this function. Requires \(n \ge 1\).
foreign import ccall "acb_dirichlet.h acb_dirichlet_isolate_hardy_z_zero"
  acb_dirichlet_isolate_hardy_z_zero :: Ptr CArf -> Ptr CArf -> Ptr CFmpz -> IO ()

-- | /_acb_dirichlet_refine_hardy_z_zero/ /res/ /a/ /b/ /prec/ 
-- 
-- Sets /res/ to the unique zero of the Hardy Z-function in the interval
-- \((a, b)\).
foreign import ccall "acb_dirichlet.h _acb_dirichlet_refine_hardy_z_zero"
  _acb_dirichlet_refine_hardy_z_zero :: Ptr CArb -> Ptr CArf -> Ptr CArf -> CLong -> IO ()

-- | /acb_dirichlet_hardy_z_zero/ /res/ /n/ /prec/ 
-- 
-- Sets /res/ to the /n/-th zero of the Hardy Z-function, requiring
-- \(n \ge 1\).
foreign import ccall "acb_dirichlet.h acb_dirichlet_hardy_z_zero"
  acb_dirichlet_hardy_z_zero :: Ptr CArb -> Ptr CFmpz -> CLong -> IO ()

-- | /acb_dirichlet_hardy_z_zeros/ /res/ /n/ /len/ /prec/ 
-- 
-- Sets the entries of /res/ to /len/ consecutive zeros of the Hardy
-- Z-function, beginning with the /n/-th zero. Requires positive /n/.
foreign import ccall "acb_dirichlet.h acb_dirichlet_hardy_z_zeros"
  acb_dirichlet_hardy_z_zeros :: Ptr CArb -> Ptr CFmpz -> CLong -> CLong -> IO ()

-- | /acb_dirichlet_zeta_zero/ /res/ /n/ /prec/ 
-- 
-- Sets /res/ to the /n/-th nontrivial zero of \(\zeta(s)\), requiring
-- \(n \ge 1\).
foreign import ccall "acb_dirichlet.h acb_dirichlet_zeta_zero"
  acb_dirichlet_zeta_zero :: Ptr CAcb -> Ptr CFmpz -> CLong -> IO ()

-- | /acb_dirichlet_zeta_zeros/ /res/ /n/ /len/ /prec/ 
-- 
-- Sets the entries of /res/ to /len/ consecutive nontrivial zeros of
-- \(\zeta(s)\) beginning with the /n/-th zero. Requires positive /n/.
foreign import ccall "acb_dirichlet.h acb_dirichlet_zeta_zeros"
  acb_dirichlet_zeta_zeros :: Ptr CAcb -> Ptr CFmpz -> CLong -> CLong -> IO ()

foreign import ccall "acb_dirichlet.h _acb_dirichlet_exact_zeta_nzeros"
  _acb_dirichlet_exact_zeta_nzeros :: Ptr CFmpz -> Ptr CArf -> IO ()

-- | /acb_dirichlet_zeta_nzeros/ /res/ /t/ /prec/ 
-- 
-- Compute the number of zeros (counted according to their multiplicities)
-- of \(\zeta(s)\) in the region \(0 < \operatorname{Im}(s) \le t\).
foreign import ccall "acb_dirichlet.h acb_dirichlet_zeta_nzeros"
  acb_dirichlet_zeta_nzeros :: Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- | /acb_dirichlet_backlund_s/ /res/ /t/ /prec/ 
-- 
-- Compute
-- \(S(t) = \frac{1}{\pi}\operatorname{arg}\zeta(\frac{1}{2} + it)\) where
-- the argument is defined by continuous variation of \(s\) in \(\zeta(s)\)
-- starting at \(s = 2\), then vertically to \(s = 2 + it\), then
-- horizontally to \(s = \frac{1}{2} + it\). In particular
-- \(\operatorname{arg}\) in this context is not the principal value of the
-- argument, and it cannot be computed directly by @acb_arg@. In practice
-- \(S(t)\) is computed as \(S(t) = N(t) - \frac{1}{\pi}\theta(t) - 1\)
-- where \(N(t)\) is @acb_dirichlet_zeta_nzeros@ and \(\theta(t)\) is
-- @acb_dirichlet_hardy_theta@.
foreign import ccall "acb_dirichlet.h acb_dirichlet_backlund_s"
  acb_dirichlet_backlund_s :: Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- | /acb_dirichlet_backlund_s_bound/ /res/ /t/ 
-- 
-- Compute an upper bound for \(|S(t)|\) quickly. Theorem 1 and the bounds
-- in (1.2) in < [Tru2014]> are used.
foreign import ccall "acb_dirichlet.h acb_dirichlet_backlund_s_bound"
  acb_dirichlet_backlund_s_bound :: Ptr CMag -> Ptr CArb -> IO ()

-- | /acb_dirichlet_zeta_nzeros_gram/ /res/ /n/ 
-- 
-- Compute \(N(g_n)\). That is, compute the number of zeros (counted
-- according to their multiplicities) of \(\zeta(s)\) in the region
-- \(0 < \operatorname{Im}(s) \le g_n\) where \(g_n\) is the /n/-th Gram
-- point. Requires \(n \ge -1\).
foreign import ccall "acb_dirichlet.h acb_dirichlet_zeta_nzeros_gram"
  acb_dirichlet_zeta_nzeros_gram :: Ptr CFmpz -> Ptr CFmpz -> IO ()

-- | /acb_dirichlet_backlund_s_gram/ /n/ 
-- 
-- Compute \(S(g_n)\) where \(g_n\) is the /n/-th Gram point. Requires
-- \(n \ge -1\).
foreign import ccall "acb_dirichlet.h acb_dirichlet_backlund_s_gram"
  acb_dirichlet_backlund_s_gram :: Ptr CFmpz -> IO CLong

-- Riemann zeta function zeros (Platt\'s method) -------------------------------

-- The following functions related to the Riemann zeta function use the
-- ideas and formulas described by David J. Platt in < [Pla2017]>.
--
-- | /acb_dirichlet_platt_scaled_lambda/ /res/ /t/ /prec/ 
-- 
-- Compute \(\Lambda(t) e^{\pi t/4}\) where
-- 
-- \[`\]
-- \[\Lambda(t) = \pi^{-\frac{it}{2}}
--                  \Gamma\left(\frac{\frac{1}{2}+it}{2}\right)
--                  \zeta\left(\frac{1}{2} + it\right)\]
-- 
-- is defined in the beginning of section 3 of < [Pla2017]>. As explained
-- in < [Pla2011]> this function has the same zeros as \(\zeta(1/2 + it)\)
-- and is real-valued by the functional equation, and the exponential
-- factor is designed to counteract the decay of the gamma factor as \(t\)
-- increases.
foreign import ccall "acb_dirichlet.h acb_dirichlet_platt_scaled_lambda"
  acb_dirichlet_platt_scaled_lambda :: Ptr CArb -> Ptr CArb -> CLong -> IO ()

foreign import ccall "acb_dirichlet.h acb_dirichlet_platt_scaled_lambda_vec"
  acb_dirichlet_platt_scaled_lambda_vec :: Ptr CArb -> Ptr CFmpz -> CLong -> CLong -> CLong -> IO ()

foreign import ccall "acb_dirichlet.h acb_dirichlet_platt_multieval"
  acb_dirichlet_platt_multieval :: Ptr CArb -> Ptr CFmpz -> CLong -> CLong -> Ptr CArb -> Ptr CFmpz -> CLong -> CLong -> CLong -> IO ()

-- | /acb_dirichlet_platt_multieval_threaded/ /res/ /T/ /A/ /B/ /h/ /J/ /K/ /sigma/ /prec/ 
-- 
-- Compute @acb_dirichlet_platt_scaled_lambda@ at \(N=AB\) points on a
-- grid, following the notation of < [Pla2017]>. The first point on the
-- grid is \(T - B/2\) and the distance between grid points is \(1/A\). The
-- product \(N=AB\) must be an even integer. The multieval versions
-- evaluate the function at all points on the grid simultaneously using
-- discrete Fourier transforms, and they require the four additional tuning
-- parameters /h/, /J/, /K/, and /sigma/. The /threaded/ multieval version
-- splits the computation over the number of threads returned by
-- /flint_get_num_threads()/, while the default multieval version chooses
-- whether to use multithreading automatically.
foreign import ccall "acb_dirichlet.h acb_dirichlet_platt_multieval_threaded"
  acb_dirichlet_platt_multieval_threaded :: Ptr CArb -> Ptr CFmpz -> CLong -> CLong -> Ptr CArb -> Ptr CFmpz -> CLong -> CLong -> CLong -> IO ()

-- | /acb_dirichlet_platt_ws_interpolation/ /res/ /deriv/ /t0/ /p/ /T/ /A/ /B/ /Ns_max/ /H/ /sigma/ /prec/ 
-- 
-- Compute @acb_dirichlet_platt_scaled_lambda@ at /t0/ by Gaussian-windowed
-- Whittaker-Shannon interpolation of points evaluated by
-- @acb_dirichlet_platt_scaled_lambda_vec@. The derivative is also
-- approximated if the output parameter /deriv/ is not /NULL/. /Ns_max/
-- defines the maximum number of supporting points to be used in the
-- interpolation on either side of /t0/. /H/ is the standard deviation of
-- the Gaussian window centered on /t0/ to be applied before the
-- interpolation. /sigma/ is an odd positive integer tuning parameter
-- \(\sigma \in 2\mathbb{Z}_{>0}+1\) used in computing error bounds.
foreign import ccall "acb_dirichlet.h acb_dirichlet_platt_ws_interpolation"
  acb_dirichlet_platt_ws_interpolation :: Ptr CArb -> Ptr CArf -> Ptr CArb -> Ptr CArb -> Ptr CFmpz -> CLong -> CLong -> CLong -> Ptr CArb -> CLong -> CLong -> IO ()

foreign import ccall "acb_dirichlet.h _acb_dirichlet_platt_local_hardy_z_zeros"
  _acb_dirichlet_platt_local_hardy_z_zeros :: Ptr CArb -> Ptr CFmpz -> CLong -> Ptr CFmpz -> CLong -> CLong -> Ptr CArb -> Ptr CFmpz -> CLong -> CLong -> CLong -> Ptr CArb -> CLong -> CLong -> IO CLong

foreign import ccall "acb_dirichlet.h acb_dirichlet_platt_local_hardy_z_zeros"
  acb_dirichlet_platt_local_hardy_z_zeros :: Ptr CArb -> Ptr CFmpz -> CLong -> CLong -> IO CLong

-- | /acb_dirichlet_platt_hardy_z_zeros/ /res/ /n/ /len/ /prec/ 
-- 
-- Sets at most the first /len/ entries of /res/ to consecutive zeros of
-- the Hardy Z-function starting with the /n/-th zero. The number of
-- obtained consecutive zeros is returned. The first two function variants
-- each make a single call to Platt\'s grid evaluation of the scaled Lambda
-- function, whereas the third variant performs as many evaluations as
-- necessary to obtain /len/ consecutive zeros. The final several
-- parameters of the underscored local variant have the same meanings as in
-- the functions @acb_dirichlet_platt_multieval@ and
-- @acb_dirichlet_platt_ws_interpolation@. The non-underscored variants
-- currently expect \(10^4 \leq n \leq 10^{23}\). The user has the option
-- of multi-threading through /flint_set_num_threads(numthreads)/.
foreign import ccall "acb_dirichlet.h acb_dirichlet_platt_hardy_z_zeros"
  acb_dirichlet_platt_hardy_z_zeros :: Ptr CArb -> Ptr CFmpz -> CLong -> CLong -> IO CLong

-- | /acb_dirichlet_platt_zeta_zeros/ /res/ /n/ /len/ /prec/ 
-- 
-- Sets at most the first /len/ entries of /res/ to consecutive zeros of
-- the Riemann zeta function starting with the /n/-th zero. The number of
-- obtained consecutive zeros is returned. It currently expects
-- \(10^4 \leq n \leq 10^{23}\). The user has the option of multi-threading
-- through /flint_set_num_threads(numthreads)/.
foreign import ccall "acb_dirichlet.h acb_dirichlet_platt_zeta_zeros"
  acb_dirichlet_platt_zeta_zeros :: Ptr CAcb -> Ptr CFmpz -> CLong -> CLong -> IO CLong

