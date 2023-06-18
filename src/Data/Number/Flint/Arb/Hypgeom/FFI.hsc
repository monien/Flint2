module Data.Number.Flint.Arb.Hypgeom.FFI (
  -- * Hypergeometric functions of real variables
  -- * Rising factorials
    _arb_hypgeom_rising_coeffs_1
  , _arb_hypgeom_rising_coeffs_2
  , _arb_hypgeom_rising_coeffs_fmpz
  , arb_hypgeom_rising_ui_forward
  , arb_hypgeom_rising_ui_bs
  , arb_hypgeom_rising_ui_rs
  , arb_hypgeom_rising_ui_rec
  , arb_hypgeom_rising_ui
  , arb_hypgeom_rising
  , arb_hypgeom_rising_ui_jet_powsum
  , arb_hypgeom_rising_ui_jet_bs
  , arb_hypgeom_rising_ui_jet_rs
  , arb_hypgeom_rising_ui_jet
  -- * Gamma function
  , _arb_hypgeom_gamma_stirling_term_bounds
  , arb_hypgeom_gamma_stirling_sum_horner
  , arb_hypgeom_gamma_stirling_sum_improved
  , arb_hypgeom_gamma_stirling
  , arb_hypgeom_gamma_taylor
  , arb_hypgeom_gamma
  , arb_hypgeom_gamma_fmpq
  , arb_hypgeom_gamma_fmpz
  , arb_hypgeom_rgamma
  , arb_hypgeom_lgamma
  -- * Binomial coefficients
  , arb_hypgeom_central_bin_ui
  -- * Generalized hypergeometric function
  , arb_hypgeom_pfq
  -- * Confluent hypergeometric functions
  , arb_hypgeom_0f1
  , arb_hypgeom_m
  , arb_hypgeom_1f1
  , arb_hypgeom_1f1_integration
  , arb_hypgeom_u
  , arb_hypgeom_u_integration
  -- * Gauss hypergeometric function
  , arb_hypgeom_2f1
  , arb_hypgeom_2f1_integration
  -- * Error functions and Fresnel integrals
  , arb_hypgeom_erf
  , _arb_hypgeom_erf_series
  , arb_hypgeom_erf_series
  , arb_hypgeom_erfc
  , _arb_hypgeom_erfc_series
  , arb_hypgeom_erfc_series
  , arb_hypgeom_erfi
  , _arb_hypgeom_erfi_series
  , arb_hypgeom_erfi_series
  , arb_hypgeom_erfinv
  , arb_hypgeom_erfcinv
  , arb_hypgeom_fresnel
  , _arb_hypgeom_fresnel_series
  , arb_hypgeom_fresnel_series
  -- * Incomplete gamma and beta functions
  , arb_hypgeom_gamma_upper
  , arb_hypgeom_gamma_upper_integration
  , _arb_hypgeom_gamma_upper_series
  , arb_hypgeom_gamma_upper_series
  , arb_hypgeom_gamma_lower
  , _arb_hypgeom_gamma_lower_series
  , arb_hypgeom_gamma_lower_series
  , arb_hypgeom_beta_lower
  , _arb_hypgeom_beta_lower_series
  , arb_hypgeom_beta_lower_series
  -- * Internal evaluation functions
  , _arb_hypgeom_gamma_lower_sum_rs_1
  , _arb_hypgeom_gamma_upper_sum_rs_1
  , _arb_hypgeom_gamma_upper_fmpq_inf_choose_N
  , _arb_hypgeom_gamma_upper_fmpq_inf_bsplit
  , _arb_hypgeom_gamma_lower_fmpq_0_choose_N
  , _arb_hypgeom_gamma_lower_fmpq_0_bsplit
  , _arb_hypgeom_gamma_upper_singular_si_choose_N
  , _arb_hypgeom_gamma_upper_singular_si_bsplit
  , _arb_gamma_upper_fmpq_step_bsplit
  -- * Exponential and trigonometric integrals
  , arb_hypgeom_expint
  , arb_hypgeom_ei
  , _arb_hypgeom_ei_series
  , arb_hypgeom_ei_series
  , _arb_hypgeom_si_asymp
  , _arb_hypgeom_si_1f2
  , arb_hypgeom_si
  , _arb_hypgeom_si_series
  , arb_hypgeom_si_series
  , _arb_hypgeom_ci_asymp
  , _arb_hypgeom_ci_2f3
  , arb_hypgeom_ci
  , _arb_hypgeom_ci_series
  , arb_hypgeom_ci_series
  , arb_hypgeom_shi
  , _arb_hypgeom_shi_series
  , arb_hypgeom_shi_series
  , arb_hypgeom_chi
  , _arb_hypgeom_chi_series
  , arb_hypgeom_chi_series
  , arb_hypgeom_li
  , _arb_hypgeom_li_series
  , arb_hypgeom_li_series
  -- * Bessel functions
  , arb_hypgeom_bessel_j
  , arb_hypgeom_bessel_y
  , arb_hypgeom_bessel_jy
  , arb_hypgeom_bessel_i
  , arb_hypgeom_bessel_i_scaled
  , arb_hypgeom_bessel_k
  , arb_hypgeom_bessel_k_scaled
  , arb_hypgeom_bessel_i_integration
  , arb_hypgeom_bessel_k_integration
  -- * Airy functions
  , arb_hypgeom_airy
  , arb_hypgeom_airy_jet
  , _arb_hypgeom_airy_series
  , arb_hypgeom_airy_series
  , arb_hypgeom_airy_zero
  -- * Coulomb wave functions
  , arb_hypgeom_coulomb
  , arb_hypgeom_coulomb_jet
  , _arb_hypgeom_coulomb_series
  , arb_hypgeom_coulomb_series
  -- * Orthogonal polynomials and functions
  , arb_hypgeom_chebyshev_t
  , arb_hypgeom_chebyshev_u
  , arb_hypgeom_jacobi_p
  , arb_hypgeom_gegenbauer_c
  , arb_hypgeom_laguerre_l
  , arb_hypgeom_hermite_h
  , arb_hypgeom_legendre_p
  , arb_hypgeom_legendre_q
  , arb_hypgeom_legendre_p_ui_deriv_bound
  , arb_hypgeom_legendre_p_ui_zero
  , arb_hypgeom_legendre_p_ui_one
  , arb_hypgeom_legendre_p_ui_asymp
  , arb_hypgeom_legendre_p_rec
  , arb_hypgeom_legendre_p_ui
  , arb_hypgeom_legendre_p_ui_root
  -- * Dilogarithm
  , arb_hypgeom_dilog
  -- * Hypergeometric sums
  , arb_hypgeom_sum_fmpq_arb_forward
  , arb_hypgeom_sum_fmpq_arb_rs
  , arb_hypgeom_sum_fmpq_arb
  , arb_hypgeom_sum_fmpq_imag_arb_forward
  , arb_hypgeom_sum_fmpq_imag_arb_rs
  , arb_hypgeom_sum_fmpq_imag_arb_bs
  , arb_hypgeom_sum_fmpq_imag_arb
) where

-- Hypergeometric functions of real variables ----------------------------------

import Foreign.Ptr
import Foreign.ForeignPtr
import Foreign.C.Types
import Foreign.C.String

import Data.Number.Flint.Fmpz
import Data.Number.Flint.Fmpq
import Data.Number.Flint.Arb.Types

-- Rising factorials -----------------------------------------------------------

-- | /_arb_hypgeom_rising_coeffs_1/ /c/ /k/ /n/ 
foreign import ccall "arb_hypgeom.h _arb_hypgeom_rising_coeffs_1"
  _arb_hypgeom_rising_coeffs_1 :: Ptr CULong -> CULong -> CLong -> IO ()
-- | /_arb_hypgeom_rising_coeffs_2/ /c/ /k/ /n/ 
foreign import ccall "arb_hypgeom.h _arb_hypgeom_rising_coeffs_2"
  _arb_hypgeom_rising_coeffs_2 :: Ptr CULong -> CULong -> CLong -> IO ()
-- | /_arb_hypgeom_rising_coeffs_fmpz/ /c/ /k/ /n/ 
--
-- Sets /c/ to the coefficients of the rising factorial polynomial
-- \((X+k)_n\). The /1/ and /2/ versions respectively compute single-word
-- and double-word coefficients, without checking for overflow, while the
-- /fmpz/ version allows arbitrarily large coefficients. These functions
-- are mostly intended for internal use; the /fmpz/ version does not use an
-- asymptotically fast algorithm. The degree /n/ must be at least 2.
foreign import ccall "arb_hypgeom.h _arb_hypgeom_rising_coeffs_fmpz"
  _arb_hypgeom_rising_coeffs_fmpz :: Ptr CFmpz -> CULong -> CLong -> IO ()

-- | /arb_hypgeom_rising_ui_forward/ /res/ /x/ /n/ /prec/ 
foreign import ccall "arb_hypgeom.h arb_hypgeom_rising_ui_forward"
  arb_hypgeom_rising_ui_forward :: Ptr CArb -> Ptr CArb -> CULong -> CLong -> IO ()
-- | /arb_hypgeom_rising_ui_bs/ /res/ /x/ /n/ /prec/ 
foreign import ccall "arb_hypgeom.h arb_hypgeom_rising_ui_bs"
  arb_hypgeom_rising_ui_bs :: Ptr CArb -> Ptr CArb -> CULong -> CLong -> IO ()
-- | /arb_hypgeom_rising_ui_rs/ /res/ /x/ /n/ /m/ /prec/ 
foreign import ccall "arb_hypgeom.h arb_hypgeom_rising_ui_rs"
  arb_hypgeom_rising_ui_rs :: Ptr CArb -> Ptr CArb -> CULong -> CULong -> CLong -> IO ()
-- | /arb_hypgeom_rising_ui_rec/ /res/ /x/ /n/ /prec/ 
foreign import ccall "arb_hypgeom.h arb_hypgeom_rising_ui_rec"
  arb_hypgeom_rising_ui_rec :: Ptr CArb -> Ptr CArb -> CULong -> CLong -> IO ()
-- | /arb_hypgeom_rising_ui/ /res/ /x/ /n/ /prec/ 
foreign import ccall "arb_hypgeom.h arb_hypgeom_rising_ui"
  arb_hypgeom_rising_ui :: Ptr CArb -> Ptr CArb -> CULong -> CLong -> IO ()
-- | /arb_hypgeom_rising/ /res/ /x/ /n/ /prec/ 
--
-- Computes the rising factorial \((x)_n\).
-- 
-- The /forward/ version uses the forward recurrence. The /bs/ version uses
-- binary splitting. The /rs/ version uses rectangular splitting. It takes
-- an extra tuning parameter /m/ which can be set to zero to choose
-- automatically. The /rec/ version chooses an algorithm automatically,
-- avoiding use of the gamma function (so that it can be used in the
-- computation of the gamma function). The default versions (/rising_ui/
-- and /rising_ui/) choose an algorithm automatically and may additionally
-- fall back on the gamma function.
foreign import ccall "arb_hypgeom.h arb_hypgeom_rising"
  arb_hypgeom_rising :: Ptr CArb -> Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- | /arb_hypgeom_rising_ui_jet_powsum/ /res/ /x/ /n/ /len/ /prec/ 
foreign import ccall "arb_hypgeom.h arb_hypgeom_rising_ui_jet_powsum"
  arb_hypgeom_rising_ui_jet_powsum :: Ptr CArb -> Ptr CArb -> CULong -> CLong -> CLong -> IO ()
-- | /arb_hypgeom_rising_ui_jet_bs/ /res/ /x/ /n/ /len/ /prec/ 
foreign import ccall "arb_hypgeom.h arb_hypgeom_rising_ui_jet_bs"
  arb_hypgeom_rising_ui_jet_bs :: Ptr CArb -> Ptr CArb -> CULong -> CLong -> CLong -> IO ()
-- | /arb_hypgeom_rising_ui_jet_rs/ /res/ /x/ /n/ /m/ /len/ /prec/ 
foreign import ccall "arb_hypgeom.h arb_hypgeom_rising_ui_jet_rs"
  arb_hypgeom_rising_ui_jet_rs :: Ptr CArb -> Ptr CArb -> CULong -> CULong -> CLong -> CLong -> IO ()
-- | /arb_hypgeom_rising_ui_jet/ /res/ /x/ /n/ /len/ /prec/ 
--
-- Computes the jet of the rising factorial \((x)_n\), truncated to length
-- /len/. In other words, constructs the polynomial
-- \((X + x)_n \in \mathbb{R}[X]\), truncated if
-- \(\operatorname{len} < n + 1\) (and zero-extended if
-- \(\operatorname{len} > n + 1\)).
-- 
-- The /powsum/ version computes the sequence of powers of /x/ and forms
-- integral linear combinations of these. The /bs/ version uses binary
-- splitting. The /rs/ version uses rectangular splitting. It takes an
-- extra tuning parameter /m/ which can be set to zero to choose
-- automatically. The default version chooses an algorithm automatically.
foreign import ccall "arb_hypgeom.h arb_hypgeom_rising_ui_jet"
  arb_hypgeom_rising_ui_jet :: Ptr CArb -> Ptr CArb -> CULong -> CLong -> CLong -> IO ()

-- Gamma function --------------------------------------------------------------

-- | /_arb_hypgeom_gamma_stirling_term_bounds/ /bound/ /zinv/ /N/ 
--
-- For \(1 \le n < N\), sets /bound/ to an exponent bounding the /n/-th
-- term in the Stirling series for the gamma function, given a precomputed
-- upper bound for \(|z|^{-1}\). This function is intended for internal use
-- and does not check for underflow or underflow in the exponents.
foreign import ccall "arb_hypgeom.h _arb_hypgeom_gamma_stirling_term_bounds"
  _arb_hypgeom_gamma_stirling_term_bounds :: Ptr CLong -> Ptr CMag -> CLong -> IO ()

-- | /arb_hypgeom_gamma_stirling_sum_horner/ /res/ /z/ /N/ /prec/ 
foreign import ccall "arb_hypgeom.h arb_hypgeom_gamma_stirling_sum_horner"
  arb_hypgeom_gamma_stirling_sum_horner :: Ptr CArb -> Ptr CArb -> CLong -> CLong -> IO ()
-- | /arb_hypgeom_gamma_stirling_sum_improved/ /res/ /z/ /N/ /K/ /prec/ 
--
-- Sets /res/ to the final sum in the Stirling series for the gamma
-- function truncated before the term with index /N/, i.e. computes
-- \(\sum_{n=1}^{N-1} B_{2n} / (2n(2n-1) z^{2n-1})\). The /horner/ version
-- uses Horner scheme with gradual precision adjustments. The /improved/
-- version uses rectangular splitting for the low-index terms and reexpands
-- the high-index terms as hypergeometric polynomials, using a splitting
-- parameter /K/ (which can be set to 0 to use a default value).
foreign import ccall "arb_hypgeom.h arb_hypgeom_gamma_stirling_sum_improved"
  arb_hypgeom_gamma_stirling_sum_improved :: Ptr CArb -> Ptr CArb -> CLong -> CLong -> CLong -> IO ()

-- | /arb_hypgeom_gamma_stirling/ /res/ /x/ /reciprocal/ /prec/ 
--
-- Sets /res/ to the gamma function of /x/ computed using the Stirling
-- series together with argument reduction. If /reciprocal/ is set, the
-- reciprocal gamma function is computed instead.
foreign import ccall "arb_hypgeom.h arb_hypgeom_gamma_stirling"
  arb_hypgeom_gamma_stirling :: Ptr CArb -> Ptr CArb -> CInt -> CLong -> IO ()

-- | /arb_hypgeom_gamma_taylor/ /res/ /x/ /reciprocal/ /prec/ 
--
-- Attempts to compute the gamma function of /x/ using Taylor series
-- together with argument reduction. This is only supported if /x/ and
-- /prec/ are both small enough. If successful, returns 1; otherwise, does
-- nothing and returns 0. If /reciprocal/ is set, the reciprocal gamma
-- function is computed instead.
foreign import ccall "arb_hypgeom.h arb_hypgeom_gamma_taylor"
  arb_hypgeom_gamma_taylor :: Ptr CArb -> Ptr CArb -> CInt -> CLong -> IO CInt

-- | /arb_hypgeom_gamma/ /res/ /x/ /prec/ 
foreign import ccall "arb_hypgeom.h arb_hypgeom_gamma"
  arb_hypgeom_gamma :: Ptr CArb -> Ptr CArb -> CLong -> IO ()
-- | /arb_hypgeom_gamma_fmpq/ /res/ /x/ /prec/ 
foreign import ccall "arb_hypgeom.h arb_hypgeom_gamma_fmpq"
  arb_hypgeom_gamma_fmpq :: Ptr CArb -> Ptr CFmpq -> CLong -> IO ()
-- | /arb_hypgeom_gamma_fmpz/ /res/ /x/ /prec/ 
--
-- Sets /res/ to the gamma function of /x/ computed using a default
-- algorithm choice.
foreign import ccall "arb_hypgeom.h arb_hypgeom_gamma_fmpz"
  arb_hypgeom_gamma_fmpz :: Ptr CArb -> Ptr CFmpz -> CLong -> IO ()

-- | /arb_hypgeom_rgamma/ /res/ /x/ /prec/ 
--
-- Sets /res/ to the reciprocal gamma function of /x/ computed using a
-- default algorithm choice.
foreign import ccall "arb_hypgeom.h arb_hypgeom_rgamma"
  arb_hypgeom_rgamma :: Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- | /arb_hypgeom_lgamma/ /res/ /x/ /prec/ 
--
-- Sets /res/ to the log-gamma function of /x/ computed using a default
-- algorithm choice.
foreign import ccall "arb_hypgeom.h arb_hypgeom_lgamma"
  arb_hypgeom_lgamma :: Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- Binomial coefficients -------------------------------------------------------

-- | /arb_hypgeom_central_bin_ui/ /res/ /n/ /prec/ 
--
-- Computes the central binomial coefficient \({2n \choose n}\).
foreign import ccall "arb_hypgeom.h arb_hypgeom_central_bin_ui"
  arb_hypgeom_central_bin_ui :: Ptr CArb -> CULong -> CLong -> IO ()

-- Generalized hypergeometric function -----------------------------------------

-- | /arb_hypgeom_pfq/ /res/ /a/ /p/ /b/ /q/ /z/ /regularized/ /prec/ 
--
-- Computes the generalized hypergeometric function \({}_pF_{q}(z)\), or
-- the regularized version if /regularized/ is set.
foreign import ccall "arb_hypgeom.h arb_hypgeom_pfq"
  arb_hypgeom_pfq :: Ptr CArb -> Ptr CArb -> CLong -> Ptr CArb -> CLong -> Ptr CArb -> CInt -> CLong -> IO ()

-- Confluent hypergeometric functions ------------------------------------------

-- | /arb_hypgeom_0f1/ /res/ /a/ /z/ /regularized/ /prec/ 
--
-- Computes the confluent hypergeometric limit function \({}_0F_1(a,z)\),
-- or \(\frac{1}{\Gamma(a)} {}_0F_1(a,z)\) if /regularized/ is set.
foreign import ccall "arb_hypgeom.h arb_hypgeom_0f1"
  arb_hypgeom_0f1 :: Ptr CArb -> Ptr CArb -> Ptr CArb -> CInt -> CLong -> IO ()

-- | /arb_hypgeom_m/ /res/ /a/ /b/ /z/ /regularized/ /prec/ 
--
-- Computes the confluent hypergeometric function
-- \(M(a,b,z) = {}_1F_1(a,b,z)\), or
-- \(\mathbf{M}(a,b,z) = \frac{1}{\Gamma(b)} {}_1F_1(a,b,z)\) if
-- /regularized/ is set.
foreign import ccall "arb_hypgeom.h arb_hypgeom_m"
  arb_hypgeom_m :: Ptr CArb -> Ptr CArb -> Ptr CArb -> Ptr CArb -> CInt -> CLong -> IO ()

-- | /arb_hypgeom_1f1/ /res/ /a/ /b/ /z/ /regularized/ /prec/ 
--
-- Alias for @arb_hypgeom_m@.
foreign import ccall "arb_hypgeom.h arb_hypgeom_1f1"
  arb_hypgeom_1f1 :: Ptr CArb -> Ptr CArb -> Ptr CArb -> Ptr CArb -> CInt -> CLong -> IO ()

-- | /arb_hypgeom_1f1_integration/ /res/ /a/ /b/ /z/ /regularized/ /prec/ 
--
-- Computes the confluent hypergeometric function using numerical
-- integration of the representation
-- 
-- \[`\]
-- \[{}_1F_1(a,b,z) = \frac{\Gamma(b)}{\Gamma(a) \Gamma(b-a)} \int_0^1 e^{zt} t^{a-1} (1-t)^{b-a-1} dt.\]
-- 
-- This algorithm can be useful if the parameters are large. This will
-- currently only return a finite enclosure if \(a \ge 1\) and
-- \(b - a \ge 1\).
foreign import ccall "arb_hypgeom.h arb_hypgeom_1f1_integration"
  arb_hypgeom_1f1_integration :: Ptr CArb -> Ptr CArb -> Ptr CArb -> Ptr CArb -> CInt -> CLong -> IO ()

-- | /arb_hypgeom_u/ /res/ /a/ /b/ /z/ /prec/ 
--
-- Computes the confluent hypergeometric function \(U(a,b,z)\).
foreign import ccall "arb_hypgeom.h arb_hypgeom_u"
  arb_hypgeom_u :: Ptr CArb -> Ptr CArb -> Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- | /arb_hypgeom_u_integration/ /res/ /a/ /b/ /z/ /regularized/ /prec/ 
--
-- Computes the confluent hypergeometric function \(U(a,b,z)\) using
-- numerical integration of the representation
-- 
-- \[`\]
-- \[U(a,b,z) = \frac{1}{\Gamma(a)} \int_0^{\infty} e^{-zt} t^{a-1} (1+t)^{b-a-1} dt.\]
-- 
-- This algorithm can be useful if the parameters are large. This will
-- currently only return a finite enclosure if \(a \ge 1\) and \(z > 0\).
foreign import ccall "arb_hypgeom.h arb_hypgeom_u_integration"
  arb_hypgeom_u_integration :: Ptr CArb -> Ptr CArb -> Ptr CArb -> Ptr CArb -> CInt -> CLong -> IO ()

-- Gauss hypergeometric function -----------------------------------------------

-- | /arb_hypgeom_2f1/ /res/ /a/ /b/ /c/ /z/ /regularized/ /prec/ 
--
-- Computes the Gauss hypergeometric function \({}_2F_1(a,b,c,z)\), or
-- \(\mathbf{F}(a,b,c,z) = \frac{1}{\Gamma(c)} {}_2F_1(a,b,c,z)\) if
-- /regularized/ is set.
-- 
-- Additional evaluation flags can be passed via the /regularized/
-- argument; see @acb_hypgeom_2f1@ for documentation.
foreign import ccall "arb_hypgeom.h arb_hypgeom_2f1"
  arb_hypgeom_2f1 :: Ptr CArb -> Ptr CArb -> Ptr CArb -> Ptr CArb -> Ptr CArb -> CInt -> CLong -> IO ()

-- | /arb_hypgeom_2f1_integration/ /res/ /a/ /b/ /z/ /regularized/ /prec/ 
--
-- Computes the Gauss hypergeometric function using numerical integration
-- of the representation
-- 
-- \[`\]
-- \[{}_2F_1(a,b,c,z) = \frac{\Gamma(a)}{\Gamma(b) \Gamma(c-b)} \int_0^1 t^{b-1} (1-t)^{c-b-1} (1-zt)^{-a} dt.\]
-- 
-- This algorithm can be useful if the parameters are large. This will
-- currently only return a finite enclosure if \(b \ge 1\) and
-- \(c - b \ge 1\) and \(z < 1\), possibly with /a/ and /b/ exchanged.
foreign import ccall "arb_hypgeom.h arb_hypgeom_2f1_integration"
  arb_hypgeom_2f1_integration :: Ptr CArb -> Ptr CArb -> Ptr CArb -> Ptr CArb -> CInt -> CLong -> IO ()

-- Error functions and Fresnel integrals ---------------------------------------

-- | /arb_hypgeom_erf/ /res/ /z/ /prec/ 
--
-- Computes the error function \(\operatorname{erf}(z)\).
foreign import ccall "arb_hypgeom.h arb_hypgeom_erf"
  arb_hypgeom_erf :: Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- | /_arb_hypgeom_erf_series/ /res/ /z/ /zlen/ /len/ /prec/ 
foreign import ccall "arb_hypgeom.h _arb_hypgeom_erf_series"
  _arb_hypgeom_erf_series :: Ptr CArb -> Ptr CArb -> CLong -> CLong -> CLong -> IO ()
-- | /arb_hypgeom_erf_series/ /res/ /z/ /len/ /prec/ 
--
-- Computes the error function of the power series /z/, truncated to length
-- /len/.
foreign import ccall "arb_hypgeom.h arb_hypgeom_erf_series"
  arb_hypgeom_erf_series :: Ptr CArbPoly -> Ptr CArbPoly -> CLong -> CLong -> IO ()

-- | /arb_hypgeom_erfc/ /res/ /z/ /prec/ 
--
-- Computes the complementary error function
-- \(\operatorname{erfc}(z) = 1 - \operatorname{erf}(z)\). This function
-- avoids catastrophic cancellation for large positive /z/.
foreign import ccall "arb_hypgeom.h arb_hypgeom_erfc"
  arb_hypgeom_erfc :: Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- | /_arb_hypgeom_erfc_series/ /res/ /z/ /zlen/ /len/ /prec/ 
foreign import ccall "arb_hypgeom.h _arb_hypgeom_erfc_series"
  _arb_hypgeom_erfc_series :: Ptr CArb -> Ptr CArb -> CLong -> CLong -> CLong -> IO ()
-- | /arb_hypgeom_erfc_series/ /res/ /z/ /len/ /prec/ 
--
-- Computes the complementary error function of the power series /z/,
-- truncated to length /len/.
foreign import ccall "arb_hypgeom.h arb_hypgeom_erfc_series"
  arb_hypgeom_erfc_series :: Ptr CArbPoly -> Ptr CArbPoly -> CLong -> CLong -> IO ()

-- | /arb_hypgeom_erfi/ /res/ /z/ /prec/ 
--
-- Computes the imaginary error function
-- \(\operatorname{erfi}(z) = -i\operatorname{erf}(iz)\).
foreign import ccall "arb_hypgeom.h arb_hypgeom_erfi"
  arb_hypgeom_erfi :: Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- | /_arb_hypgeom_erfi_series/ /res/ /z/ /zlen/ /len/ /prec/ 
foreign import ccall "arb_hypgeom.h _arb_hypgeom_erfi_series"
  _arb_hypgeom_erfi_series :: Ptr CArb -> Ptr CArb -> CLong -> CLong -> CLong -> IO ()
-- | /arb_hypgeom_erfi_series/ /res/ /z/ /len/ /prec/ 
--
-- Computes the imaginary error function of the power series /z/, truncated
-- to length /len/.
foreign import ccall "arb_hypgeom.h arb_hypgeom_erfi_series"
  arb_hypgeom_erfi_series :: Ptr CArbPoly -> Ptr CArbPoly -> CLong -> CLong -> IO ()

-- | /arb_hypgeom_erfinv/ /res/ /z/ /prec/ 
foreign import ccall "arb_hypgeom.h arb_hypgeom_erfinv"
  arb_hypgeom_erfinv :: Ptr CArb -> Ptr CArb -> CLong -> IO ()
-- | /arb_hypgeom_erfcinv/ /res/ /z/ /prec/ 
--
-- Computes the inverse error function \(\operatorname{erf}^{-1}(z)\) or
-- inverse complementary error function \(\operatorname{erfc}^{-1}(z)\).
foreign import ccall "arb_hypgeom.h arb_hypgeom_erfcinv"
  arb_hypgeom_erfcinv :: Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- | /arb_hypgeom_fresnel/ /res1/ /res2/ /z/ /normalized/ /prec/ 
--
-- Sets /res1/ to the Fresnel sine integral \(S(z)\) and /res2/ to the
-- Fresnel cosine integral \(C(z)\). Optionally, just a single function can
-- be computed by passing /NULL/ as the other output variable. The
-- definition \(S(z) = \int_0^z \sin(t^2) dt\) is used if /normalized/ is
-- 0, and \(S(z) = \int_0^z \sin(\tfrac{1}{2} \pi t^2) dt\) is used if
-- /normalized/ is 1 (the latter is the Abramowitz & Stegun convention).
-- \(C(z)\) is defined analogously.
foreign import ccall "arb_hypgeom.h arb_hypgeom_fresnel"
  arb_hypgeom_fresnel :: Ptr CArb -> Ptr CArb -> Ptr CArb -> CInt -> CLong -> IO ()

-- | /_arb_hypgeom_fresnel_series/ /res1/ /res2/ /z/ /zlen/ /normalized/ /len/ /prec/ 
foreign import ccall "arb_hypgeom.h _arb_hypgeom_fresnel_series"
  _arb_hypgeom_fresnel_series :: Ptr CArb -> Ptr CArb -> Ptr CArb -> CLong -> CInt -> CLong -> CLong -> IO ()
-- | /arb_hypgeom_fresnel_series/ /res1/ /res2/ /z/ /normalized/ /len/ /prec/ 
--
-- Sets /res1/ to the Fresnel sine integral and /res2/ to the Fresnel
-- cosine integral of the power series /z/, truncated to length /len/.
-- Optionally, just a single function can be computed by passing /NULL/ as
-- the other output variable.
foreign import ccall "arb_hypgeom.h arb_hypgeom_fresnel_series"
  arb_hypgeom_fresnel_series :: Ptr CArbPoly -> Ptr CArbPoly -> Ptr CArbPoly -> CInt -> CLong -> CLong -> IO ()

-- Incomplete gamma and beta functions -----------------------------------------

-- | /arb_hypgeom_gamma_upper/ /res/ /s/ /z/ /regularized/ /prec/ 
--
-- If /regularized/ is 0, computes the upper incomplete gamma function
-- \(\Gamma(s,z)\).
-- 
-- If /regularized/ is 1, computes the regularized upper incomplete gamma
-- function \(Q(s,z) = \Gamma(s,z) / \Gamma(s)\).
-- 
-- If /regularized/ is 2, computes the generalized exponential integral
-- \(z^{-s} \Gamma(s,z) = E_{1-s}(z)\) instead (this option is mainly
-- intended for internal use; @arb_hypgeom_expint@ is the intended
-- interface for computing the exponential integral).
foreign import ccall "arb_hypgeom.h arb_hypgeom_gamma_upper"
  arb_hypgeom_gamma_upper :: Ptr CArb -> Ptr CArb -> Ptr CArb -> CInt -> CLong -> IO ()

-- | /arb_hypgeom_gamma_upper_integration/ /res/ /s/ /z/ /regularized/ /prec/ 
--
-- Computes the upper incomplete gamma function using numerical
-- integration.
foreign import ccall "arb_hypgeom.h arb_hypgeom_gamma_upper_integration"
  arb_hypgeom_gamma_upper_integration :: Ptr CArb -> Ptr CArb -> Ptr CArb -> CInt -> CLong -> IO ()

-- | /_arb_hypgeom_gamma_upper_series/ /res/ /s/ /z/ /zlen/ /regularized/ /n/ /prec/ 
foreign import ccall "arb_hypgeom.h _arb_hypgeom_gamma_upper_series"
  _arb_hypgeom_gamma_upper_series :: Ptr CArb -> Ptr CArb -> Ptr CArb -> CLong -> CInt -> CLong -> CLong -> IO ()
-- | /arb_hypgeom_gamma_upper_series/ /res/ /s/ /z/ /regularized/ /n/ /prec/ 
--
-- Sets /res/ to an upper incomplete gamma function where /s/ is a constant
-- and /z/ is a power series, truncated to length /n/. The /regularized/
-- argument has the same interpretation as in @arb_hypgeom_gamma_upper@.
foreign import ccall "arb_hypgeom.h arb_hypgeom_gamma_upper_series"
  arb_hypgeom_gamma_upper_series :: Ptr CArbPoly -> Ptr CArb -> Ptr CArbPoly -> CInt -> CLong -> CLong -> IO ()

-- | /arb_hypgeom_gamma_lower/ /res/ /s/ /z/ /regularized/ /prec/ 
--
-- If /regularized/ is 0, computes the lower incomplete gamma function
-- \(\gamma(s,z) = \frac{z^s}{s} {}_1F_1(s, s+1, -z)\).
-- 
-- If /regularized/ is 1, computes the regularized lower incomplete gamma
-- function \(P(s,z) = \gamma(s,z) / \Gamma(s)\).
-- 
-- If /regularized/ is 2, computes a further regularized lower incomplete
-- gamma function \(\gamma^{*}(s,z) = z^{-s} P(s,z)\).
foreign import ccall "arb_hypgeom.h arb_hypgeom_gamma_lower"
  arb_hypgeom_gamma_lower :: Ptr CArb -> Ptr CArb -> Ptr CArb -> CInt -> CLong -> IO ()

-- | /_arb_hypgeom_gamma_lower_series/ /res/ /s/ /z/ /zlen/ /regularized/ /n/ /prec/ 
foreign import ccall "arb_hypgeom.h _arb_hypgeom_gamma_lower_series"
  _arb_hypgeom_gamma_lower_series :: Ptr CArb -> Ptr CArb -> Ptr CArb -> CLong -> CInt -> CLong -> CLong -> IO ()
-- | /arb_hypgeom_gamma_lower_series/ /res/ /s/ /z/ /regularized/ /n/ /prec/ 
--
-- Sets /res/ to an lower incomplete gamma function where /s/ is a constant
-- and /z/ is a power series, truncated to length /n/. The /regularized/
-- argument has the same interpretation as in @arb_hypgeom_gamma_lower@.
foreign import ccall "arb_hypgeom.h arb_hypgeom_gamma_lower_series"
  arb_hypgeom_gamma_lower_series :: Ptr CArbPoly -> Ptr CArb -> Ptr CArbPoly -> CInt -> CLong -> CLong -> IO ()

-- | /arb_hypgeom_beta_lower/ /res/ /a/ /b/ /z/ /regularized/ /prec/ 
--
-- Computes the (lower) incomplete beta function, defined by
-- \(B(a,b;z) = \int_0^z t^{a-1} (1-t)^{b-1}\), optionally the regularized
-- incomplete beta function \(I(a,b;z) = B(a,b;z) / B(a,b;1)\).
foreign import ccall "arb_hypgeom.h arb_hypgeom_beta_lower"
  arb_hypgeom_beta_lower :: Ptr CArb -> Ptr CArb -> Ptr CArb -> Ptr CArb -> CInt -> CLong -> IO ()

-- | /_arb_hypgeom_beta_lower_series/ /res/ /a/ /b/ /z/ /zlen/ /regularized/ /n/ /prec/ 
foreign import ccall "arb_hypgeom.h _arb_hypgeom_beta_lower_series"
  _arb_hypgeom_beta_lower_series :: Ptr CArb -> Ptr CArb -> Ptr CArb -> Ptr CArb -> CLong -> CInt -> CLong -> CLong -> IO ()
-- | /arb_hypgeom_beta_lower_series/ /res/ /a/ /b/ /z/ /regularized/ /n/ /prec/ 
--
-- Sets /res/ to the lower incomplete beta function \(B(a,b;z)\)
-- (optionally the regularized version \(I(a,b;z)\)) where /a/ and /b/ are
-- constants and /z/ is a power series, truncating the result to length
-- /n/. The underscore method requires positive lengths and does not
-- support aliasing.
foreign import ccall "arb_hypgeom.h arb_hypgeom_beta_lower_series"
  arb_hypgeom_beta_lower_series :: Ptr CArbPoly -> Ptr CArb -> Ptr CArb -> Ptr CArbPoly -> CInt -> CLong -> CLong -> IO ()

-- Internal evaluation functions -----------------------------------------------

-- | /_arb_hypgeom_gamma_lower_sum_rs_1/ /res/ /p/ /q/ /z/ /N/ /prec/ 
--
-- Computes \(\sum_{k=0}^{N-1} z^k / (a)_k\) where \(a = p/q\) using
-- rectangular splitting. It is assumed that \(p + qN\) fits in a limb.
foreign import ccall "arb_hypgeom.h _arb_hypgeom_gamma_lower_sum_rs_1"
  _arb_hypgeom_gamma_lower_sum_rs_1 :: Ptr CArb -> CULong -> CULong -> Ptr CArb -> CLong -> CLong -> IO ()

-- | /_arb_hypgeom_gamma_upper_sum_rs_1/ /res/ /p/ /q/ /z/ /N/ /prec/ 
--
-- Computes \(\sum_{k=0}^{N-1} (a)_k / z^k\) where \(a = p/q\) using
-- rectangular splitting. It is assumed that \(p + qN\) fits in a limb.
foreign import ccall "arb_hypgeom.h _arb_hypgeom_gamma_upper_sum_rs_1"
  _arb_hypgeom_gamma_upper_sum_rs_1 :: Ptr CArb -> CULong -> CULong -> Ptr CArb -> CLong -> CLong -> IO ()

-- | /_arb_hypgeom_gamma_upper_fmpq_inf_choose_N/ /err/ /a/ /z/ /abs_tol/ 
--
-- Returns number of terms /N/ and sets /err/ to the truncation error for
-- evaluating \(\Gamma(a,z)\) using the asymptotic series at infinity,
-- targeting an absolute tolerance of /abs_tol/. The error may be set to
-- /err/ if the tolerance cannot be achieved. Assumes that /z/ is positive.
foreign import ccall "arb_hypgeom.h _arb_hypgeom_gamma_upper_fmpq_inf_choose_N"
  _arb_hypgeom_gamma_upper_fmpq_inf_choose_N :: Ptr CMag -> Ptr CFmpq -> Ptr CArb -> Ptr CMag -> IO CLong

-- | /_arb_hypgeom_gamma_upper_fmpq_inf_bsplit/ /res/ /a/ /z/ /N/ /prec/ 
--
-- Sets /res/ to the approximation of \(\Gamma(a,z)\) obtained by
-- truncating the asymptotic series at infinity before term /N/. The
-- truncation error bound has to be added separately.
foreign import ccall "arb_hypgeom.h _arb_hypgeom_gamma_upper_fmpq_inf_bsplit"
  _arb_hypgeom_gamma_upper_fmpq_inf_bsplit :: Ptr CArb -> Ptr CFmpq -> Ptr CArb -> CLong -> CLong -> IO ()

-- | /_arb_hypgeom_gamma_lower_fmpq_0_choose_N/ /err/ /a/ /z/ /abs_tol/ 
--
-- Returns number of terms /N/ and sets /err/ to the truncation error for
-- evaluating \(\gamma(a,z)\) using the Taylor series at zero, targeting an
-- absolute tolerance of /abs_tol/. Assumes that /z/ is positive.
foreign import ccall "arb_hypgeom.h _arb_hypgeom_gamma_lower_fmpq_0_choose_N"
  _arb_hypgeom_gamma_lower_fmpq_0_choose_N :: Ptr CMag -> Ptr CFmpq -> Ptr CArb -> Ptr CMag -> IO CLong

-- | /_arb_hypgeom_gamma_lower_fmpq_0_bsplit/ /res/ /a/ /z/ /N/ /prec/ 
--
-- Sets /res/ to the approximation of \(\gamma(a,z)\) obtained by
-- truncating the Taylor series at zero before term /N/. The truncation
-- error bound has to be added separately.
foreign import ccall "arb_hypgeom.h _arb_hypgeom_gamma_lower_fmpq_0_bsplit"
  _arb_hypgeom_gamma_lower_fmpq_0_bsplit :: Ptr CArb -> Ptr CFmpq -> Ptr CArb -> CLong -> CLong -> IO ()

-- | /_arb_hypgeom_gamma_upper_singular_si_choose_N/ /err/ /n/ /z/ /abs_tol/ 
--
-- Returns number of terms /N/ and sets /err/ to the truncation error for
-- evaluating \(\Gamma(-n,z)\) using the Taylor series at zero, targeting
-- an absolute tolerance of /abs_tol/.
foreign import ccall "arb_hypgeom.h _arb_hypgeom_gamma_upper_singular_si_choose_N"
  _arb_hypgeom_gamma_upper_singular_si_choose_N :: Ptr CMag -> CLong -> Ptr CArb -> Ptr CMag -> IO CLong

-- | /_arb_hypgeom_gamma_upper_singular_si_bsplit/ /res/ /n/ /z/ /N/ /prec/ 
--
-- Sets /res/ to the approximation of \(\Gamma(-n,z)\) obtained by
-- truncating the Taylor series at zero before term /N/. The truncation
-- error bound has to be added separately.
foreign import ccall "arb_hypgeom.h _arb_hypgeom_gamma_upper_singular_si_bsplit"
  _arb_hypgeom_gamma_upper_singular_si_bsplit :: Ptr CArb -> CLong -> Ptr CArb -> CLong -> CLong -> IO ()

-- | /_arb_gamma_upper_fmpq_step_bsplit/ /Gz1/ /a/ /z0/ /z1/ /Gz0/ /expmz0/ /abs_tol/ /prec/ 
--
-- Given /Gz0/ and /expmz0/ representing the values \(\Gamma(a,z_0)\) and
-- \(\exp(-z_0)\), computes \(\Gamma(a,z_1)\) using the Taylor series at
-- \(z_0\) evaluated using binary splitting, targeting an absolute error of
-- /abs_tol/. Assumes that \(z_0\) and \(z_1\) are positive.
foreign import ccall "arb_hypgeom.h _arb_gamma_upper_fmpq_step_bsplit"
  _arb_gamma_upper_fmpq_step_bsplit :: Ptr CArb -> Ptr CFmpq -> Ptr CArb -> Ptr CArb -> Ptr CArb -> Ptr CArb -> Ptr CMag -> CLong -> IO ()

-- Exponential and trigonometric integrals -------------------------------------

-- | /arb_hypgeom_expint/ /res/ /s/ /z/ /prec/ 
--
-- Computes the generalized exponential integral \(E_s(z)\).
foreign import ccall "arb_hypgeom.h arb_hypgeom_expint"
  arb_hypgeom_expint :: Ptr CArb -> Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- | /arb_hypgeom_ei/ /res/ /z/ /prec/ 
--
-- Computes the exponential integral \(\operatorname{Ei}(z)\).
foreign import ccall "arb_hypgeom.h arb_hypgeom_ei"
  arb_hypgeom_ei :: Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- | /_arb_hypgeom_ei_series/ /res/ /z/ /zlen/ /len/ /prec/ 
foreign import ccall "arb_hypgeom.h _arb_hypgeom_ei_series"
  _arb_hypgeom_ei_series :: Ptr CArb -> Ptr CArb -> CLong -> CLong -> CLong -> IO ()
-- | /arb_hypgeom_ei_series/ /res/ /z/ /len/ /prec/ 
--
-- Computes the exponential integral of the power series /z/, truncated to
-- length /len/.
foreign import ccall "arb_hypgeom.h arb_hypgeom_ei_series"
  arb_hypgeom_ei_series :: Ptr CArbPoly -> Ptr CArbPoly -> CLong -> CLong -> IO ()

-- | /_arb_hypgeom_si_asymp/ /res/ /z/ /N/ /prec/ 
foreign import ccall "arb_hypgeom.h _arb_hypgeom_si_asymp"
  _arb_hypgeom_si_asymp :: Ptr CArb -> Ptr CArb -> CLong -> CLong -> IO ()
-- | /_arb_hypgeom_si_1f2/ /res/ /z/ /N/ /wp/ /prec/ 
foreign import ccall "arb_hypgeom.h _arb_hypgeom_si_1f2"
  _arb_hypgeom_si_1f2 :: Ptr CArb -> Ptr CArb -> CLong -> CLong -> CLong -> IO ()
-- | /arb_hypgeom_si/ /res/ /z/ /prec/ 
--
-- Computes the sine integral \(\operatorname{Si}(z)\).
foreign import ccall "arb_hypgeom.h arb_hypgeom_si"
  arb_hypgeom_si :: Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- | /_arb_hypgeom_si_series/ /res/ /z/ /zlen/ /len/ /prec/ 
foreign import ccall "arb_hypgeom.h _arb_hypgeom_si_series"
  _arb_hypgeom_si_series :: Ptr CArb -> Ptr CArb -> CLong -> CLong -> CLong -> IO ()
-- | /arb_hypgeom_si_series/ /res/ /z/ /len/ /prec/ 
--
-- Computes the sine integral of the power series /z/, truncated to length
-- /len/.
foreign import ccall "arb_hypgeom.h arb_hypgeom_si_series"
  arb_hypgeom_si_series :: Ptr CArbPoly -> Ptr CArbPoly -> CLong -> CLong -> IO ()

-- | /_arb_hypgeom_ci_asymp/ /res/ /z/ /N/ /prec/ 
foreign import ccall "arb_hypgeom.h _arb_hypgeom_ci_asymp"
  _arb_hypgeom_ci_asymp :: Ptr CArb -> Ptr CArb -> CLong -> CLong -> IO ()
-- | /_arb_hypgeom_ci_2f3/ /res/ /z/ /N/ /wp/ /prec/ 
foreign import ccall "arb_hypgeom.h _arb_hypgeom_ci_2f3"
  _arb_hypgeom_ci_2f3 :: Ptr CArb -> Ptr CArb -> CLong -> CLong -> CLong -> IO ()
-- | /arb_hypgeom_ci/ /res/ /z/ /prec/ 
--
-- Computes the cosine integral \(\operatorname{Ci}(z)\). The result is
-- indeterminate if \(z < 0\) since the value of the function would be
-- complex.
foreign import ccall "arb_hypgeom.h arb_hypgeom_ci"
  arb_hypgeom_ci :: Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- | /_arb_hypgeom_ci_series/ /res/ /z/ /zlen/ /len/ /prec/ 
foreign import ccall "arb_hypgeom.h _arb_hypgeom_ci_series"
  _arb_hypgeom_ci_series :: Ptr CArb -> Ptr CArb -> CLong -> CLong -> CLong -> IO ()
-- | /arb_hypgeom_ci_series/ /res/ /z/ /len/ /prec/ 
--
-- Computes the cosine integral of the power series /z/, truncated to
-- length /len/.
foreign import ccall "arb_hypgeom.h arb_hypgeom_ci_series"
  arb_hypgeom_ci_series :: Ptr CArbPoly -> Ptr CArbPoly -> CLong -> CLong -> IO ()

-- | /arb_hypgeom_shi/ /res/ /z/ /prec/ 
--
-- Computes the hyperbolic sine integral
-- \(\operatorname{Shi}(z) = -i \operatorname{Si}(iz)\).
foreign import ccall "arb_hypgeom.h arb_hypgeom_shi"
  arb_hypgeom_shi :: Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- | /_arb_hypgeom_shi_series/ /res/ /z/ /zlen/ /len/ /prec/ 
foreign import ccall "arb_hypgeom.h _arb_hypgeom_shi_series"
  _arb_hypgeom_shi_series :: Ptr CArb -> Ptr CArb -> CLong -> CLong -> CLong -> IO ()
-- | /arb_hypgeom_shi_series/ /res/ /z/ /len/ /prec/ 
--
-- Computes the hyperbolic sine integral of the power series /z/, truncated
-- to length /len/.
foreign import ccall "arb_hypgeom.h arb_hypgeom_shi_series"
  arb_hypgeom_shi_series :: Ptr CArbPoly -> Ptr CArbPoly -> CLong -> CLong -> IO ()

-- | /arb_hypgeom_chi/ /res/ /z/ /prec/ 
--
-- Computes the hyperbolic cosine integral \(\operatorname{Chi}(z)\). The
-- result is indeterminate if \(z < 0\) since the value of the function
-- would be complex.
foreign import ccall "arb_hypgeom.h arb_hypgeom_chi"
  arb_hypgeom_chi :: Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- | /_arb_hypgeom_chi_series/ /res/ /z/ /zlen/ /len/ /prec/ 
foreign import ccall "arb_hypgeom.h _arb_hypgeom_chi_series"
  _arb_hypgeom_chi_series :: Ptr CArb -> Ptr CArb -> CLong -> CLong -> CLong -> IO ()
-- | /arb_hypgeom_chi_series/ /res/ /z/ /len/ /prec/ 
--
-- Computes the hyperbolic cosine integral of the power series /z/,
-- truncated to length /len/.
foreign import ccall "arb_hypgeom.h arb_hypgeom_chi_series"
  arb_hypgeom_chi_series :: Ptr CArbPoly -> Ptr CArbPoly -> CLong -> CLong -> IO ()

-- | /arb_hypgeom_li/ /res/ /z/ /offset/ /prec/ 
--
-- If /offset/ is zero, computes the logarithmic integral
-- \(\operatorname{li}(z) = \operatorname{Ei}(\log(z))\).
-- 
-- If /offset/ is nonzero, computes the offset logarithmic integral
-- \(\operatorname{Li}(z) = \operatorname{li}(z) - \operatorname{li}(2)\).
-- 
-- The result is indeterminate if \(z < 0\) since the value of the function
-- would be complex.
foreign import ccall "arb_hypgeom.h arb_hypgeom_li"
  arb_hypgeom_li :: Ptr CArb -> Ptr CArb -> CInt -> CLong -> IO ()

-- | /_arb_hypgeom_li_series/ /res/ /z/ /zlen/ /offset/ /len/ /prec/ 
foreign import ccall "arb_hypgeom.h _arb_hypgeom_li_series"
  _arb_hypgeom_li_series :: Ptr CArb -> Ptr CArb -> CLong -> CInt -> CLong -> CLong -> IO ()
-- | /arb_hypgeom_li_series/ /res/ /z/ /offset/ /len/ /prec/ 
--
-- Computes the logarithmic integral (optionally the offset version) of the
-- power series /z/, truncated to length /len/.
foreign import ccall "arb_hypgeom.h arb_hypgeom_li_series"
  arb_hypgeom_li_series :: Ptr CArbPoly -> Ptr CArbPoly -> CInt -> CLong -> CLong -> IO ()

-- Bessel functions ------------------------------------------------------------

-- | /arb_hypgeom_bessel_j/ /res/ /nu/ /z/ /prec/ 
--
-- Computes the Bessel function of the first kind \(J_{\nu}(z)\).
foreign import ccall "arb_hypgeom.h arb_hypgeom_bessel_j"
  arb_hypgeom_bessel_j :: Ptr CArb -> Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- | /arb_hypgeom_bessel_y/ /res/ /nu/ /z/ /prec/ 
--
-- Computes the Bessel function of the second kind \(Y_{\nu}(z)\).
foreign import ccall "arb_hypgeom.h arb_hypgeom_bessel_y"
  arb_hypgeom_bessel_y :: Ptr CArb -> Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- | /arb_hypgeom_bessel_jy/ /res1/ /res2/ /nu/ /z/ /prec/ 
--
-- Sets /res1/ to \(J_{\nu}(z)\) and /res2/ to \(Y_{\nu}(z)\), computed
-- simultaneously.
foreign import ccall "arb_hypgeom.h arb_hypgeom_bessel_jy"
  arb_hypgeom_bessel_jy :: Ptr CArb -> Ptr CArb -> Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- | /arb_hypgeom_bessel_i/ /res/ /nu/ /z/ /prec/ 
--
-- Computes the modified Bessel function of the first kind
-- \(I_{\nu}(z) = z^{\nu} (iz)^{-\nu} J_{\nu}(iz)\).
foreign import ccall "arb_hypgeom.h arb_hypgeom_bessel_i"
  arb_hypgeom_bessel_i :: Ptr CArb -> Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- | /arb_hypgeom_bessel_i_scaled/ /res/ /nu/ /z/ /prec/ 
--
-- Computes the function \(e^{-z} I_{\nu}(z)\).
foreign import ccall "arb_hypgeom.h arb_hypgeom_bessel_i_scaled"
  arb_hypgeom_bessel_i_scaled :: Ptr CArb -> Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- | /arb_hypgeom_bessel_k/ /res/ /nu/ /z/ /prec/ 
--
-- Computes the modified Bessel function of the second kind \(K_{\nu}(z)\).
foreign import ccall "arb_hypgeom.h arb_hypgeom_bessel_k"
  arb_hypgeom_bessel_k :: Ptr CArb -> Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- | /arb_hypgeom_bessel_k_scaled/ /res/ /nu/ /z/ /prec/ 
--
-- Computes the function \(e^{z} K_{\nu}(z)\).
foreign import ccall "arb_hypgeom.h arb_hypgeom_bessel_k_scaled"
  arb_hypgeom_bessel_k_scaled :: Ptr CArb -> Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- | /arb_hypgeom_bessel_i_integration/ /res/ /nu/ /z/ /scaled/ /prec/ 
foreign import ccall "arb_hypgeom.h arb_hypgeom_bessel_i_integration"
  arb_hypgeom_bessel_i_integration :: Ptr CArb -> Ptr CArb -> Ptr CArb -> CInt -> CLong -> IO ()
-- | /arb_hypgeom_bessel_k_integration/ /res/ /nu/ /z/ /scaled/ /prec/ 
--
-- Computes the modified Bessel functions using numerical integration.
foreign import ccall "arb_hypgeom.h arb_hypgeom_bessel_k_integration"
  arb_hypgeom_bessel_k_integration :: Ptr CArb -> Ptr CArb -> Ptr CArb -> CInt -> CLong -> IO ()

-- Airy functions --------------------------------------------------------------

-- | /arb_hypgeom_airy/ /ai/ /ai_prime/ /bi/ /bi_prime/ /z/ /prec/ 
--
-- Computes the Airy functions
-- \((\operatorname{Ai}(z), \operatorname{Ai}'(z), \operatorname{Bi}(z), \operatorname{Bi}'(z))\)
-- simultaneously. Any of the four function values can be omitted by
-- passing /NULL/ for the unwanted output variables, speeding up the
-- evaluation.
foreign import ccall "arb_hypgeom.h arb_hypgeom_airy"
  arb_hypgeom_airy :: Ptr CArb -> Ptr CArb -> Ptr CArb -> Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- | /arb_hypgeom_airy_jet/ /ai/ /bi/ /z/ /len/ /prec/ 
--
-- Writes to /ai/ and /bi/ the respective Taylor expansions of the Airy
-- functions at the point /z/, truncated to length /len/. Either of the
-- outputs can be /NULL/ to avoid computing that function. The variable /z/
-- is not allowed to be aliased with the outputs. To simplify the
-- implementation, this method does not compute the series expansions of
-- the primed versions directly; these are easily obtained by computing one
-- extra coefficient and differentiating the output with
-- @_arb_poly_derivative@.
foreign import ccall "arb_hypgeom.h arb_hypgeom_airy_jet"
  arb_hypgeom_airy_jet :: Ptr CArb -> Ptr CArb -> Ptr CArb -> CLong -> CLong -> IO ()

-- | /_arb_hypgeom_airy_series/ /ai/ /ai_prime/ /bi/ /bi_prime/ /z/ /zlen/ /len/ /prec/ 
foreign import ccall "arb_hypgeom.h _arb_hypgeom_airy_series"
  _arb_hypgeom_airy_series :: Ptr CArb -> Ptr CArb -> Ptr CArb -> Ptr CArb -> Ptr CArb -> CLong -> CLong -> CLong -> IO ()
-- | /arb_hypgeom_airy_series/ /ai/ /ai_prime/ /bi/ /bi_prime/ /z/ /len/ /prec/ 
--
-- Computes the Airy functions evaluated at the power series /z/, truncated
-- to length /len/. As with the other Airy methods, any of the outputs can
-- be /NULL/.
foreign import ccall "arb_hypgeom.h arb_hypgeom_airy_series"
  arb_hypgeom_airy_series :: Ptr CArbPoly -> Ptr CArbPoly -> Ptr CArbPoly -> Ptr CArbPoly -> Ptr CArbPoly -> CLong -> CLong -> IO ()

-- | /arb_hypgeom_airy_zero/ /a/ /a_prime/ /b/ /b_prime/ /n/ /prec/ 
--
-- Computes the /n/-th real zero \(a_n\), \(a'_n\), \(b_n\), or \(b'_n\)
-- for the respective Airy function or Airy function derivative. Any
-- combination of the four output variables can be /NULL/. The zeros are
-- indexed by increasing magnitude, starting with \(n = 1\) to follow the
-- convention in the literature. An index /n/ that is not positive is
-- invalid input. The implementation uses asymptotic expansions for the
-- zeros < [PS1991]> together with the interval Newton method for
-- refinement.
foreign import ccall "arb_hypgeom.h arb_hypgeom_airy_zero"
  arb_hypgeom_airy_zero :: Ptr CArb -> Ptr CArb -> Ptr CArb -> Ptr CArb -> Ptr CFmpz -> CLong -> IO ()

-- Coulomb wave functions ------------------------------------------------------

-- | /arb_hypgeom_coulomb/ /F/ /G/ /l/ /eta/ /z/ /prec/ 
--
-- Writes to /F/, /G/ the values of the respective Coulomb wave functions
-- \(F_{\ell}(\eta,z)\) and \(G_{\ell}(\eta,z)\). Either of the outputs can
-- be /NULL/.
foreign import ccall "arb_hypgeom.h arb_hypgeom_coulomb"
  arb_hypgeom_coulomb :: Ptr CArb -> Ptr CArb -> Ptr CArb -> Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- | /arb_hypgeom_coulomb_jet/ /F/ /G/ /l/ /eta/ /z/ /len/ /prec/ 
--
-- Writes to /F/, /G/ the respective Taylor expansions of the Coulomb wave
-- functions at the point /z/, truncated to length /len/. Either of the
-- outputs can be /NULL/.
foreign import ccall "arb_hypgeom.h arb_hypgeom_coulomb_jet"
  arb_hypgeom_coulomb_jet :: Ptr CArb -> Ptr CArb -> Ptr CArb -> Ptr CArb -> Ptr CArb -> CLong -> CLong -> IO ()

-- | /_arb_hypgeom_coulomb_series/ /F/ /G/ /l/ /eta/ /z/ /zlen/ /len/ /prec/ 
foreign import ccall "arb_hypgeom.h _arb_hypgeom_coulomb_series"
  _arb_hypgeom_coulomb_series :: Ptr CArb -> Ptr CArb -> Ptr CArb -> Ptr CArb -> Ptr CArb -> CLong -> CLong -> CLong -> IO ()
-- | /arb_hypgeom_coulomb_series/ /F/ /G/ /l/ /eta/ /z/ /len/ /prec/ 
--
-- Computes the Coulomb wave functions evaluated at the power series /z/,
-- truncated to length /len/. Either of the outputs can be /NULL/.
foreign import ccall "arb_hypgeom.h arb_hypgeom_coulomb_series"
  arb_hypgeom_coulomb_series :: Ptr CArbPoly -> Ptr CArbPoly -> Ptr CArb -> Ptr CArb -> Ptr CArbPoly -> CLong -> CLong -> IO ()

-- Orthogonal polynomials and functions ----------------------------------------

-- | /arb_hypgeom_chebyshev_t/ /res/ /nu/ /z/ /prec/ 
foreign import ccall "arb_hypgeom.h arb_hypgeom_chebyshev_t"
  arb_hypgeom_chebyshev_t :: Ptr CArb -> Ptr CArb -> Ptr CArb -> CLong -> IO ()
-- | /arb_hypgeom_chebyshev_u/ /res/ /nu/ /z/ /prec/ 
foreign import ccall "arb_hypgeom.h arb_hypgeom_chebyshev_u"
  arb_hypgeom_chebyshev_u :: Ptr CArb -> Ptr CArb -> Ptr CArb -> CLong -> IO ()
-- | /arb_hypgeom_jacobi_p/ /res/ /n/ /a/ /b/ /z/ /prec/ 
foreign import ccall "arb_hypgeom.h arb_hypgeom_jacobi_p"
  arb_hypgeom_jacobi_p :: Ptr CArb -> Ptr CArb -> Ptr CArb -> Ptr CArb -> Ptr CArb -> CLong -> IO ()
-- | /arb_hypgeom_gegenbauer_c/ /res/ /n/ /m/ /z/ /prec/ 
foreign import ccall "arb_hypgeom.h arb_hypgeom_gegenbauer_c"
  arb_hypgeom_gegenbauer_c :: Ptr CArb -> Ptr CArb -> Ptr CArb -> Ptr CArb -> CLong -> IO ()
-- | /arb_hypgeom_laguerre_l/ /res/ /n/ /m/ /z/ /prec/ 
foreign import ccall "arb_hypgeom.h arb_hypgeom_laguerre_l"
  arb_hypgeom_laguerre_l :: Ptr CArb -> Ptr CArb -> Ptr CArb -> Ptr CArb -> CLong -> IO ()
-- | /arb_hypgeom_hermite_h/ /res/ /nu/ /z/ /prec/ 
--
-- Computes Chebyshev, Jacobi, Gegenbauer, Laguerre or Hermite polynomials,
-- or their extensions to non-integer orders.
foreign import ccall "arb_hypgeom.h arb_hypgeom_hermite_h"
  arb_hypgeom_hermite_h :: Ptr CArb -> Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- | /arb_hypgeom_legendre_p/ /res/ /n/ /m/ /z/ /type/ /prec/ 
foreign import ccall "arb_hypgeom.h arb_hypgeom_legendre_p"
  arb_hypgeom_legendre_p :: Ptr CArb -> Ptr CArb -> Ptr CArb -> Ptr CArb -> CInt -> CLong -> IO ()
-- | /arb_hypgeom_legendre_q/ /res/ /n/ /m/ /z/ /type/ /prec/ 
--
-- Computes Legendre functions of the first and second kind. See
-- @acb_hypgeom_legendre_p@ and @acb_hypgeom_legendre_q@ for definitions.
foreign import ccall "arb_hypgeom.h arb_hypgeom_legendre_q"
  arb_hypgeom_legendre_q :: Ptr CArb -> Ptr CArb -> Ptr CArb -> Ptr CArb -> CInt -> CLong -> IO ()

-- | /arb_hypgeom_legendre_p_ui_deriv_bound/ /dp/ /dp2/ /n/ /x/ /x2sub1/ 
--
-- Sets /dp/ to an upper bound for \(P'_n(x)\) and /dp2/ to an upper bound
-- for \(P''_n(x)\) given /x/ assumed to represent a real number with
-- \(|x| \le 1\). The variable /x2sub1/ must contain the precomputed value
-- \(1-x^2\) (or \(x^2-1\)). This method is used internally to bound the
-- propagated error for Legendre polynomials.
foreign import ccall "arb_hypgeom.h arb_hypgeom_legendre_p_ui_deriv_bound"
  arb_hypgeom_legendre_p_ui_deriv_bound :: Ptr CMag -> Ptr CMag -> CULong -> Ptr CArb -> Ptr CArb -> IO ()

-- | /arb_hypgeom_legendre_p_ui_zero/ /res/ /res_prime/ /n/ /x/ /K/ /prec/ 
foreign import ccall "arb_hypgeom.h arb_hypgeom_legendre_p_ui_zero"
  arb_hypgeom_legendre_p_ui_zero :: Ptr CArb -> Ptr CArb -> CULong -> Ptr CArb -> CLong -> CLong -> IO ()
-- | /arb_hypgeom_legendre_p_ui_one/ /res/ /res_prime/ /n/ /x/ /K/ /prec/ 
foreign import ccall "arb_hypgeom.h arb_hypgeom_legendre_p_ui_one"
  arb_hypgeom_legendre_p_ui_one :: Ptr CArb -> Ptr CArb -> CULong -> Ptr CArb -> CLong -> CLong -> IO ()
-- | /arb_hypgeom_legendre_p_ui_asymp/ /res/ /res_prime/ /n/ /x/ /K/ /prec/ 
foreign import ccall "arb_hypgeom.h arb_hypgeom_legendre_p_ui_asymp"
  arb_hypgeom_legendre_p_ui_asymp :: Ptr CArb -> Ptr CArb -> CULong -> Ptr CArb -> CLong -> CLong -> IO ()
-- | /arb_hypgeom_legendre_p_rec/ /res/ /res_prime/ /n/ /x/ /prec/ 
foreign import ccall "arb_hypgeom.h arb_hypgeom_legendre_p_rec"
  arb_hypgeom_legendre_p_rec :: Ptr CArb -> Ptr CArb -> CULong -> Ptr CArb -> CLong -> IO ()
-- | /arb_hypgeom_legendre_p_ui/ /res/ /res_prime/ /n/ /x/ /prec/ 
--
-- Evaluates the ordinary Legendre polynomial \(P_n(x)\). If /res_prime/ is
-- non-NULL, simultaneously evaluates the derivative \(P'_n(x)\).
-- 
-- The overall algorithm is described in < [JM2018]>.
-- 
-- The versions /zero/, /one/ respectively use the hypergeometric series
-- expansions at \(x = 0\) and \(x = 1\) while the /asymp/ version uses an
-- asymptotic series on \((-1,1)\) intended for large /n/. The parameter
-- /K/ specifies the exact number of expansion terms to use (if the series
-- expansion truncated at this point does not give the exact polynomial, an
-- error bound is computed automatically). The asymptotic expansion with
-- error bounds is given in < [Bog2012]>. The /rec/ version uses the
-- forward recurrence implemented using fixed-point arithmetic; it is only
-- intended for the interval \((-1,1)\), moderate /n/ and modest precision.
-- 
-- The default version attempts to choose the best algorithm automatically.
-- It also estimates the amount of cancellation in the hypergeometric
-- series and increases the working precision to compensate, bounding the
-- propagated error using derivative bounds.
foreign import ccall "arb_hypgeom.h arb_hypgeom_legendre_p_ui"
  arb_hypgeom_legendre_p_ui :: Ptr CArb -> Ptr CArb -> CULong -> Ptr CArb -> CLong -> IO ()

-- | /arb_hypgeom_legendre_p_ui_root/ /res/ /weight/ /n/ /k/ /prec/ 
--
-- Sets /res/ to the /k/-th root of the Legendre polynomial \(P_n(x)\). We
-- index the roots in decreasing order
-- 
-- \[`\]
-- \[1 > x_0 > x_1 > \ldots > x_{n-1} > -1\]
-- 
-- (which corresponds to ordering the roots of \(P_n(\cos(\theta))\) in
-- order of increasing \(\theta\)). If /weight/ is non-NULL, it is set to
-- the weight corresponding to the node \(x_k\) for Gaussian quadrature on
-- \([-1,1]\). Note that only \(\lceil n / 2 \rceil\) roots need to be
-- computed, since the remaining roots are given by \(x_k = -x_{n-1-k}\).
-- 
-- We compute an enclosing interval using an asymptotic approximation
-- followed by some number of Newton iterations, using the error bounds
-- given in < [Pet1999]>. If very high precision is requested, the root is
-- subsequently refined using interval Newton steps with doubling working
-- precision.
foreign import ccall "arb_hypgeom.h arb_hypgeom_legendre_p_ui_root"
  arb_hypgeom_legendre_p_ui_root :: Ptr CArb -> Ptr CArb -> CULong -> CULong -> CLong -> IO ()

-- Dilogarithm -----------------------------------------------------------------

-- | /arb_hypgeom_dilog/ /res/ /z/ /prec/ 
--
-- Computes the dilogarithm \(\operatorname{Li}_2(z)\).
foreign import ccall "arb_hypgeom.h arb_hypgeom_dilog"
  arb_hypgeom_dilog :: Ptr CArb -> Ptr CArb -> CLong -> IO ()

-- Hypergeometric sums ---------------------------------------------------------

-- | /arb_hypgeom_sum_fmpq_arb_forward/ /res/ /a/ /alen/ /b/ /blen/ /z/ /reciprocal/ /N/ /prec/ 
foreign import ccall "arb_hypgeom.h arb_hypgeom_sum_fmpq_arb_forward"
  arb_hypgeom_sum_fmpq_arb_forward :: Ptr CArb -> Ptr CFmpq -> CLong -> Ptr CFmpq -> CLong -> Ptr CArb -> CInt -> CLong -> CLong -> IO ()
-- | /arb_hypgeom_sum_fmpq_arb_rs/ /res/ /a/ /alen/ /b/ /blen/ /z/ /reciprocal/ /N/ /prec/ 
foreign import ccall "arb_hypgeom.h arb_hypgeom_sum_fmpq_arb_rs"
  arb_hypgeom_sum_fmpq_arb_rs :: Ptr CArb -> Ptr CFmpq -> CLong -> Ptr CFmpq -> CLong -> Ptr CArb -> CInt -> CLong -> CLong -> IO ()
-- | /arb_hypgeom_sum_fmpq_arb/ /res/ /a/ /alen/ /b/ /blen/ /z/ /reciprocal/ /N/ /prec/ 
--
-- Sets /res/ to the finite hypergeometric sum
-- \(\sum_{n=0}^{N-1} (\textbf{a})_n z^n / (\textbf{b})_n\) where
-- \(\textbf{x}_n = (x_1)_n (x_2)_n \cdots\), given vectors of rational
-- parameters /a/ (of length /alen/) and /b/ (of length /blen/). If
-- /reciprocal/ is set, replace \(z\) by \(1 / z\). The /forward/ version
-- uses the forward recurrence, optimized by delaying divisions, the /rs/
-- version uses rectangular splitting, and the default version uses an
-- automatic algorithm choice.
foreign import ccall "arb_hypgeom.h arb_hypgeom_sum_fmpq_arb"
  arb_hypgeom_sum_fmpq_arb :: Ptr CArb -> Ptr CFmpq -> CLong -> Ptr CFmpq -> CLong -> Ptr CArb -> CInt -> CLong -> CLong -> IO ()

-- | /arb_hypgeom_sum_fmpq_imag_arb_forward/ /res1/ /res2/ /a/ /alen/ /b/ /blen/ /z/ /reciprocal/ /N/ /prec/ 
foreign import ccall "arb_hypgeom.h arb_hypgeom_sum_fmpq_imag_arb_forward"
  arb_hypgeom_sum_fmpq_imag_arb_forward :: Ptr CArb -> Ptr CArb -> Ptr CFmpq -> CLong -> Ptr CFmpq -> CLong -> Ptr CArb -> CInt -> CLong -> CLong -> IO ()
-- | /arb_hypgeom_sum_fmpq_imag_arb_rs/ /res1/ /res2/ /a/ /alen/ /b/ /blen/ /z/ /reciprocal/ /N/ /prec/ 
foreign import ccall "arb_hypgeom.h arb_hypgeom_sum_fmpq_imag_arb_rs"
  arb_hypgeom_sum_fmpq_imag_arb_rs :: Ptr CArb -> Ptr CArb -> Ptr CFmpq -> CLong -> Ptr CFmpq -> CLong -> Ptr CArb -> CInt -> CLong -> CLong -> IO ()
-- | /arb_hypgeom_sum_fmpq_imag_arb_bs/ /res1/ /res2/ /a/ /alen/ /b/ /blen/ /z/ /reciprocal/ /N/ /prec/ 
foreign import ccall "arb_hypgeom.h arb_hypgeom_sum_fmpq_imag_arb_bs"
  arb_hypgeom_sum_fmpq_imag_arb_bs :: Ptr CArb -> Ptr CArb -> Ptr CFmpq -> CLong -> Ptr CFmpq -> CLong -> Ptr CArb -> CInt -> CLong -> CLong -> IO ()
-- | /arb_hypgeom_sum_fmpq_imag_arb/ /res1/ /res2/ /a/ /alen/ /b/ /blen/ /z/ /reciprocal/ /N/ /prec/ 
--
-- Sets /res1/ and /res2/ to the real and imaginary part of the finite
-- hypergeometric sum
-- \(\sum_{n=0}^{N-1} (\textbf{a})_n (i z)^n / (\textbf{b})_n\). If
-- /reciprocal/ is set, replace \(z\) by \(1 / z\).
foreign import ccall "arb_hypgeom.h arb_hypgeom_sum_fmpq_imag_arb"
  arb_hypgeom_sum_fmpq_imag_arb :: Ptr CArb -> Ptr CArb -> Ptr CFmpq -> CLong -> Ptr CFmpq -> CLong -> Ptr CArb -> CInt -> CLong -> CLong -> IO ()

