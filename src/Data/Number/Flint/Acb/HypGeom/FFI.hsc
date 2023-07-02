{-# language
    CApiFFI
  , EmptyDataDecls
  , FlexibleInstances
  , ForeignFunctionInterface
  , MultiParamTypeClasses
  , TupleSections
  , TypeFamilies
  #-}

module Data.Number.Flint.Acb.Hypgeom.FFI (
  -- * Hypergeometric functions of complex variables
  -- * Rising factorials
    acb_hypgeom_rising_ui_forward
  , acb_hypgeom_rising_ui_bs
  , acb_hypgeom_rising_ui_rs
  , acb_hypgeom_rising_ui_rec
  , acb_hypgeom_rising_ui
  , acb_hypgeom_rising
  , acb_hypgeom_rising_ui_jet_powsum
  , acb_hypgeom_rising_ui_jet_bs
  , acb_hypgeom_rising_ui_jet_rs
  , acb_hypgeom_rising_ui_jet
  , acb_hypgeom_log_rising_ui
  , acb_hypgeom_log_rising_ui_jet
  -- * Gamma function
  , acb_hypgeom_gamma_stirling_sum_horner
  , acb_hypgeom_gamma_stirling_sum_improved
  , acb_hypgeom_gamma_stirling
  , acb_hypgeom_gamma_taylor
  , acb_hypgeom_gamma
  , acb_hypgeom_rgamma
  , acb_hypgeom_lgamma
  -- * Convergent series
  , acb_hypgeom_pfq_bound_factor
  , acb_hypgeom_pfq_choose_n
  , acb_hypgeom_pfq_sum_forward
  , acb_hypgeom_pfq_sum_rs
  , acb_hypgeom_pfq_sum_bs
  , acb_hypgeom_pfq_sum_fme
  , acb_hypgeom_pfq_sum
  , acb_hypgeom_pfq_sum_bs_invz
  , acb_hypgeom_pfq_sum_invz
  , acb_hypgeom_pfq_direct
  , acb_hypgeom_pfq_series_sum_forward
  , acb_hypgeom_pfq_series_sum_bs
  , acb_hypgeom_pfq_series_sum_rs
  , acb_hypgeom_pfq_series_sum
  , acb_hypgeom_pfq_series_direct
  -- * Asymptotic series
  , acb_hypgeom_u_asymp
  , acb_hypgeom_u_use_asymp
  -- * Generalized hypergeometric function
  , acb_hypgeom_pfq
  -- * Confluent hypergeometric functions
  , acb_hypgeom_u_1f1_series
  , acb_hypgeom_u_1f1
  , acb_hypgeom_u
  , acb_hypgeom_m_asymp
  , acb_hypgeom_m_1f1
  , acb_hypgeom_m
  , acb_hypgeom_1f1
  , acb_hypgeom_0f1_asymp
  , acb_hypgeom_0f1_direct
  , acb_hypgeom_0f1
  -- * Error functions and Fresnel integrals
  , acb_hypgeom_erf_propagated_error
  , acb_hypgeom_erf_1f1a
  , acb_hypgeom_erf_1f1b
  , acb_hypgeom_erf_asymp
  , acb_hypgeom_erf
  , _acb_hypgeom_erf_series
  , acb_hypgeom_erf_series
  , acb_hypgeom_erfc
  , _acb_hypgeom_erfc_series
  , acb_hypgeom_erfc_series
  , acb_hypgeom_erfi
  , _acb_hypgeom_erfi_series
  , acb_hypgeom_erfi_series
  , acb_hypgeom_fresnel
  , _acb_hypgeom_fresnel_series
  , acb_hypgeom_fresnel_series
  -- * Bessel functions
  , acb_hypgeom_bessel_j_asymp
  , acb_hypgeom_bessel_j_0f1
  , acb_hypgeom_bessel_j
  , acb_hypgeom_bessel_y
  , acb_hypgeom_bessel_jy
  -- * Modified Bessel functions
  , acb_hypgeom_bessel_i_asymp
  , acb_hypgeom_bessel_i_0f1
  , acb_hypgeom_bessel_i
  , acb_hypgeom_bessel_i_scaled
  , acb_hypgeom_bessel_k_asymp
  , acb_hypgeom_bessel_k_0f1_series
  , acb_hypgeom_bessel_k_0f1
  , acb_hypgeom_bessel_k
  , acb_hypgeom_bessel_k_scaled
  -- * Airy functions
  , acb_hypgeom_airy_direct
  , acb_hypgeom_airy_asymp
  , acb_hypgeom_airy_bound
  , acb_hypgeom_airy
  , acb_hypgeom_airy_jet
  , _acb_hypgeom_airy_series
  , acb_hypgeom_airy_series
  -- * Coulomb wave functions
  , acb_hypgeom_coulomb
  , acb_hypgeom_coulomb_jet
  , _acb_hypgeom_coulomb_series
  , acb_hypgeom_coulomb_series
  -- * Incomplete gamma and beta functions
  , acb_hypgeom_gamma_upper_asymp
  , acb_hypgeom_gamma_upper_1f1a
  , acb_hypgeom_gamma_upper_1f1b
  , acb_hypgeom_gamma_upper_singular
  , acb_hypgeom_gamma_upper
  , _acb_hypgeom_gamma_upper_series
  , acb_hypgeom_gamma_upper_series
  , acb_hypgeom_gamma_lower
  , _acb_hypgeom_gamma_lower_series
  , acb_hypgeom_gamma_lower_series
  , acb_hypgeom_beta_lower
  , _acb_hypgeom_beta_lower_series
  , acb_hypgeom_beta_lower_series
  -- * Exponential and trigonometric integrals
  , acb_hypgeom_expint
  , acb_hypgeom_ei_asymp
  , acb_hypgeom_ei_2f2
  , acb_hypgeom_ei
  , _acb_hypgeom_ei_series
  , acb_hypgeom_ei_series
  , acb_hypgeom_si_asymp
  , acb_hypgeom_si_1f2
  , acb_hypgeom_si
  , _acb_hypgeom_si_series
  , acb_hypgeom_si_series
  , acb_hypgeom_ci_asymp
  , acb_hypgeom_ci_2f3
  , acb_hypgeom_ci
  , _acb_hypgeom_ci_series
  , acb_hypgeom_ci_series
  , acb_hypgeom_shi
  , _acb_hypgeom_shi_series
  , acb_hypgeom_shi_series
  , acb_hypgeom_chi_asymp
  , acb_hypgeom_chi_2f3
  , acb_hypgeom_chi
  , _acb_hypgeom_chi_series
  , acb_hypgeom_chi_series
  , acb_hypgeom_li
  , _acb_hypgeom_li_series
  , acb_hypgeom_li_series
  -- * Gauss hypergeometric function
  , acb_hypgeom_2f1_continuation
  , acb_hypgeom_2f1_series_direct
  , acb_hypgeom_2f1_direct
  , acb_hypgeom_2f1_transform
  , acb_hypgeom_2f1_transform_limit
  , acb_hypgeom_2f1_corner
  , acb_hypgeom_2f1_choose
  , acb_hypgeom_2f1
  -- * Orthogonal polynomials and functions
  , acb_hypgeom_chebyshev_t
  , acb_hypgeom_chebyshev_u
  , acb_hypgeom_jacobi_p
  , acb_hypgeom_gegenbauer_c
  , acb_hypgeom_laguerre_l
  , acb_hypgeom_hermite_h
  , acb_hypgeom_legendre_p
  , acb_hypgeom_legendre_q
  , acb_hypgeom_legendre_p_uiui_rec
  , acb_hypgeom_spherical_y
  -- * Dilogarithm
  , acb_hypgeom_dilog_zero_taylor
  , acb_hypgeom_dilog_zero
  , acb_hypgeom_dilog_transform
  , acb_hypgeom_dilog_continuation
  , acb_hypgeom_dilog_bitburst
  , acb_hypgeom_dilog
) where 

-- Hypergeometric functions of complex variables -------------------------------

import Foreign.C.Types
import Foreign.ForeignPtr
import Foreign.Ptr ( Ptr, FunPtr )

import Data.Number.Flint.Arb
import Data.Number.Flint.Arb.Types
import Data.Number.Flint.Acb
import Data.Number.Flint.Acb.Types
import Data.Number.Flint.Acb.Poly

-- Rising factorials -----------------------------------------------------------

-- | /acb_hypgeom_rising_ui_forward/ /res/ /x/ /n/ /prec/ 
foreign import ccall "acb_hypgeom.h acb_hypgeom_rising_ui_forward"
  acb_hypgeom_rising_ui_forward :: Ptr CAcb -> Ptr CAcb -> CULong -> CLong -> IO ()
-- | /acb_hypgeom_rising_ui_bs/ /res/ /x/ /n/ /prec/ 
foreign import ccall "acb_hypgeom.h acb_hypgeom_rising_ui_bs"
  acb_hypgeom_rising_ui_bs :: Ptr CAcb -> Ptr CAcb -> CULong -> CLong -> IO ()
-- | /acb_hypgeom_rising_ui_rs/ /res/ /x/ /n/ /m/ /prec/ 
foreign import ccall "acb_hypgeom.h acb_hypgeom_rising_ui_rs"
  acb_hypgeom_rising_ui_rs :: Ptr CAcb -> Ptr CAcb -> CULong -> CULong -> CLong -> IO ()
-- | /acb_hypgeom_rising_ui_rec/ /res/ /x/ /n/ /prec/ 
foreign import ccall "acb_hypgeom.h acb_hypgeom_rising_ui_rec"
  acb_hypgeom_rising_ui_rec :: Ptr CAcb -> Ptr CAcb -> CULong -> CLong -> IO ()
-- | /acb_hypgeom_rising_ui/ /res/ /x/ /n/ /prec/ 
foreign import ccall "acb_hypgeom.h acb_hypgeom_rising_ui"
  acb_hypgeom_rising_ui :: Ptr CAcb -> Ptr CAcb -> CULong -> CLong -> IO ()
-- | /acb_hypgeom_rising/ /res/ /x/ /n/ /prec/ 
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
foreign import ccall "acb_hypgeom.h acb_hypgeom_rising"
  acb_hypgeom_rising :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_hypgeom_rising_ui_jet_powsum/ /res/ /x/ /n/ /len/ /prec/ 
foreign import ccall "acb_hypgeom.h acb_hypgeom_rising_ui_jet_powsum"
  acb_hypgeom_rising_ui_jet_powsum :: Ptr CAcb -> Ptr CAcb -> CULong -> CLong -> CLong -> IO ()
-- | /acb_hypgeom_rising_ui_jet_bs/ /res/ /x/ /n/ /len/ /prec/ 
foreign import ccall "acb_hypgeom.h acb_hypgeom_rising_ui_jet_bs"
  acb_hypgeom_rising_ui_jet_bs :: Ptr CAcb -> Ptr CAcb -> CULong -> CLong -> CLong -> IO ()
-- | /acb_hypgeom_rising_ui_jet_rs/ /res/ /x/ /n/ /m/ /len/ /prec/ 
foreign import ccall "acb_hypgeom.h acb_hypgeom_rising_ui_jet_rs"
  acb_hypgeom_rising_ui_jet_rs :: Ptr CAcb -> Ptr CAcb -> CULong -> CULong -> CLong -> CLong -> IO ()
-- | /acb_hypgeom_rising_ui_jet/ /res/ /x/ /n/ /len/ /prec/ 
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
foreign import ccall "acb_hypgeom.h acb_hypgeom_rising_ui_jet"
  acb_hypgeom_rising_ui_jet :: Ptr CAcb -> Ptr CAcb -> CULong -> CLong -> CLong -> IO ()

-- | /acb_hypgeom_log_rising_ui/ /res/ /x/ /n/ /prec/ 
--
-- Computes the log-rising factorial
-- \(\log \, (x)_n = \sum_{k=0}^{n-1} \log(x+k)\).
-- 
-- This first computes the ordinary rising factorial and then determines
-- the branch correction \(2 \pi i m\) with respect to the principal
-- logarithm. The correction is computed using Hare\'s algorithm in
-- floating-point arithmetic if this is safe; otherwise, a direct
-- computation of \(\sum_{k=0}^{n-1} \arg(x+k)\) is used as a fallback.
foreign import ccall "acb_hypgeom.h acb_hypgeom_log_rising_ui"
  acb_hypgeom_log_rising_ui :: Ptr CAcb -> Ptr CAcb -> CULong -> CLong -> IO ()

-- | /acb_hypgeom_log_rising_ui_jet/ /res/ /x/ /n/ /len/ /prec/ 
--
-- Computes the jet of the log-rising factorial \(\log \, (x)_n\),
-- truncated to length /len/.
foreign import ccall "acb_hypgeom.h acb_hypgeom_log_rising_ui_jet"
  acb_hypgeom_log_rising_ui_jet :: Ptr CAcb -> Ptr CAcb -> CULong -> CLong -> CLong -> IO ()

-- Gamma function --------------------------------------------------------------

-- | /acb_hypgeom_gamma_stirling_sum_horner/ /s/ /z/ /N/ /prec/ 
foreign import ccall "acb_hypgeom.h acb_hypgeom_gamma_stirling_sum_horner"
  acb_hypgeom_gamma_stirling_sum_horner :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> IO ()
-- | /acb_hypgeom_gamma_stirling_sum_improved/ /s/ /z/ /N/ /K/ /prec/ 
--
-- Sets /res/ to the final sum in the Stirling series for the gamma
-- function truncated before the term with index /N/, i.e. computes
-- \(\sum_{n=1}^{N-1} B_{2n} / (2n(2n-1) z^{2n-1})\). The /horner/ version
-- uses Horner scheme with gradual precision adjustments. The /improved/
-- version uses rectangular splitting for the low-index terms and reexpands
-- the high-index terms as hypergeometric polynomials, using a splitting
-- parameter /K/ (which can be set to 0 to use a default value).
foreign import ccall "acb_hypgeom.h acb_hypgeom_gamma_stirling_sum_improved"
  acb_hypgeom_gamma_stirling_sum_improved :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> CLong -> IO ()

-- | /acb_hypgeom_gamma_stirling/ /res/ /x/ /reciprocal/ /prec/ 
--
-- Sets /res/ to the gamma function of /x/ computed using the Stirling
-- series together with argument reduction. If /reciprocal/ is set, the
-- reciprocal gamma function is computed instead.
foreign import ccall "acb_hypgeom.h acb_hypgeom_gamma_stirling"
  acb_hypgeom_gamma_stirling :: Ptr CAcb -> Ptr CAcb -> CInt -> CLong -> IO ()

-- | /acb_hypgeom_gamma_taylor/ /res/ /x/ /reciprocal/ /prec/ 
--
-- Attempts to compute the gamma function of /x/ using Taylor series
-- together with argument reduction. This is only supported if /x/ and
-- /prec/ are both small enough. If successful, returns 1; otherwise, does
-- nothing and returns 0. If /reciprocal/ is set, the reciprocal gamma
-- function is computed instead.
foreign import ccall "acb_hypgeom.h acb_hypgeom_gamma_taylor"
  acb_hypgeom_gamma_taylor :: Ptr CAcb -> Ptr CAcb -> CInt -> CLong -> IO CInt

-- | /acb_hypgeom_gamma/ /res/ /x/ /prec/ 
--
-- Sets /res/ to the gamma function of /x/ computed using a default
-- algorithm choice.
foreign import ccall "acb_hypgeom.h acb_hypgeom_gamma"
  acb_hypgeom_gamma :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_hypgeom_rgamma/ /res/ /x/ /prec/ 
--
-- Sets /res/ to the reciprocal gamma function of /x/ computed using a
-- default algorithm choice.
foreign import ccall "acb_hypgeom.h acb_hypgeom_rgamma"
  acb_hypgeom_rgamma :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_hypgeom_lgamma/ /res/ /x/ /prec/ 
--
-- Sets /res/ to the principal branch of the log-gamma function of /x/
-- computed using a default algorithm choice.
foreign import ccall "acb_hypgeom.h acb_hypgeom_lgamma"
  acb_hypgeom_lgamma :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- Convergent series -----------------------------------------------------------

-- In this section, we define
--
-- \[`\]
-- \[T(k) = \frac{\prod_{i=0}^{p-1} (a_i)_k}{\prod_{i=0}^{q-1} (b_i)_k} z^k\]
--
-- and
--
-- \[`\]
-- \[{}_pf_{q}(a_0,\ldots,a_{p-1}; b_0 \ldots b_{q-1}; z) = {}_{p+1}F_{q}(a_0,\ldots,a_{p-1},1; b_0 \ldots b_{q-1}; z) = \sum_{k=0}^{\infty} T(k)\]
--
-- For the conventional generalized hypergeometric function {}_pF_{q},
-- compute \({}_pf_{q+1}\) with the explicit parameter \(b_q = 1\), or
-- remove a 1 from the \(a_i\) parameters if there is one.
--
-- | /acb_hypgeom_pfq_bound_factor/ /C/ /a/ /p/ /b/ /q/ /z/ /n/ 
--
-- Computes a factor /C/ such that
-- \(\left|\sum_{k=n}^{\infty} T(k)\right| \le C |T(n)|\). See
-- @algorithms_hypergeometric_convergent@. As currently implemented, the
-- bound becomes infinite when \(n\) is too small, even if the series
-- converges.
foreign import ccall "acb_hypgeom.h acb_hypgeom_pfq_bound_factor"
  acb_hypgeom_pfq_bound_factor :: Ptr CMag -> Ptr CAcb -> CLong -> Ptr CAcb -> CLong -> Ptr CAcb -> CULong -> IO ()

-- | /acb_hypgeom_pfq_choose_n/ /a/ /p/ /b/ /q/ /z/ /prec/ 
--
-- Heuristically attempts to choose a number of terms /n/ to sum of a
-- hypergeometric series at a working precision of /prec/ bits.
-- 
-- Uses double precision arithmetic internally. As currently implemented,
-- it can fail to produce a good result if the parameters are extremely
-- large or extremely close to nonpositive integers.
-- 
-- Numerical cancellation is assumed to be significant, so truncation is
-- done when the current term is /prec/ bits smaller than the largest
-- encountered term.
-- 
-- This function will also attempt to pick a reasonable truncation point
-- for divergent series.
foreign import ccall "acb_hypgeom.h acb_hypgeom_pfq_choose_n"
  acb_hypgeom_pfq_choose_n :: Ptr CAcb -> CLong -> Ptr CAcb -> CLong -> Ptr CAcb -> CLong -> IO CLong

-- | /acb_hypgeom_pfq_sum_forward/ /s/ /t/ /a/ /p/ /b/ /q/ /z/ /n/ /prec/ 
--
foreign import ccall "acb_hypgeom.h acb_hypgeom_pfq_sum_forward"
  acb_hypgeom_pfq_sum_forward :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> Ptr CAcb -> CLong -> Ptr CAcb -> CLong -> CLong -> IO ()

-- | /acb_hypgeom_pfq_sum_rs/ /s/ /t/ /a/ /p/ /b/ /q/ /z/ /n/ /prec/ 
--
foreign import ccall "acb_hypgeom.h acb_hypgeom_pfq_sum_rs"
  acb_hypgeom_pfq_sum_rs :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> Ptr CAcb -> CLong -> Ptr CAcb -> CLong -> CLong -> IO ()

-- | /acb_hypgeom_pfq_sum_bs/ /s/ /t/ /a/ /p/ /b/ /q/ /z/ /n/ /prec/ 
--
foreign import ccall "acb_hypgeom.h acb_hypgeom_pfq_sum_bs"
  acb_hypgeom_pfq_sum_bs :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> Ptr CAcb -> CLong -> Ptr CAcb -> CLong -> CLong -> IO ()

-- | /acb_hypgeom_pfq_sum_fme/ /s/ /t/ /a/ /p/ /b/ /q/ /z/ /n/ /prec/ 
--
foreign import ccall "acb_hypgeom.h acb_hypgeom_pfq_sum_fme"
  acb_hypgeom_pfq_sum_fme :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> Ptr CAcb -> CLong -> Ptr CAcb -> CLong -> CLong -> IO ()

-- | /acb_hypgeom_pfq_sum/ /s/ /t/ /a/ /p/ /b/ /q/ /z/ /n/ /prec/ 
--
-- Computes \(s = \sum_{k=0}^{n-1} T(k)\) and \(t = T(n)\). Does not allow
-- aliasing between input and output variables. We require \(n \ge 0\).
-- 
-- The /forward/ version computes the sum using forward recurrence.
-- 
-- The /bs/ version computes the sum using binary splitting.
-- 
-- The /rs/ version computes the sum in reverse order using rectangular
-- splitting. It only computes a magnitude bound for the value of /t/.
-- 
-- The /fme/ version uses fast multipoint evaluation.
-- 
-- The default version automatically chooses an algorithm depending on the
-- inputs.
foreign import ccall "acb_hypgeom.h acb_hypgeom_pfq_sum"
  acb_hypgeom_pfq_sum :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> Ptr CAcb -> CLong -> Ptr CAcb -> CLong -> CLong -> IO ()

-- | /acb_hypgeom_pfq_sum_bs_invz/ /s/ /t/ /a/ /p/ /b/ /q/ /w/ /n/ /prec/ 
--
foreign import ccall "acb_hypgeom.h acb_hypgeom_pfq_sum_bs_invz"
  acb_hypgeom_pfq_sum_bs_invz :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> Ptr CAcb -> CLong -> Ptr CAcb -> CLong -> CLong -> IO ()

-- | /acb_hypgeom_pfq_sum_invz/ /s/ /t/ /a/ /p/ /b/ /q/ /z/ /w/ /n/ /prec/ 
--
-- Like @acb_hypgeom_pfq_sum@, but taking advantage of \(w = 1/z\) possibly
-- having few bits.
foreign import ccall "acb_hypgeom.h acb_hypgeom_pfq_sum_invz"
  acb_hypgeom_pfq_sum_invz :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> Ptr CAcb -> CLong -> Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> IO ()

-- | /acb_hypgeom_pfq_direct/ /res/ /a/ /p/ /b/ /q/ /z/ /n/ /prec/ 
--
-- Computes
-- 
-- \[{}_pf_{q}(z)
--     = \sum_{k=0}^{\infty} T(k)
--     = \sum_{k=0}^{n-1} T(k) + \varepsilon\]
-- 
-- directly from the defining series, including a rigorous bound for the
-- truncation error \(\varepsilon\) in the output.
-- 
-- If \(n < 0\), this function chooses a number of terms automatically
-- using @acb_hypgeom_pfq_choose_n@.
foreign import ccall "acb_hypgeom.h acb_hypgeom_pfq_direct"
  acb_hypgeom_pfq_direct :: Ptr CAcb -> Ptr CAcb -> CLong -> Ptr CAcb -> CLong -> Ptr CAcb -> CLong -> CLong -> IO ()

-- | /acb_hypgeom_pfq_series_sum_forward/ /s/ /t/ /a/ /p/ /b/ /q/ /z/ /regularized/ /n/ /len/ /prec/ 
--
foreign import ccall "acb_hypgeom.h acb_hypgeom_pfq_series_sum_forward"
  acb_hypgeom_pfq_series_sum_forward :: Ptr CAcbPoly -> Ptr CAcbPoly -> Ptr (Ptr CAcbPoly) -> CLong -> Ptr (Ptr CAcbPoly) -> CLong -> Ptr CAcbPoly -> CInt -> CLong -> CLong -> CLong -> IO ()

-- | /acb_hypgeom_pfq_series_sum_bs/ /s/ /t/ /a/ /p/ /b/ /q/ /z/ /regularized/ /n/ /len/ /prec/ 
--
foreign import ccall "acb_hypgeom.h acb_hypgeom_pfq_series_sum_bs"
  acb_hypgeom_pfq_series_sum_bs :: Ptr CAcbPoly -> Ptr CAcbPoly -> Ptr (Ptr CAcbPoly) -> CLong -> Ptr (Ptr CAcbPoly) -> CLong -> Ptr CAcbPoly -> CInt -> CLong -> CLong -> CLong -> IO ()

-- | /acb_hypgeom_pfq_series_sum_rs/ /s/ /t/ /a/ /p/ /b/ /q/ /z/ /regularized/ /n/ /len/ /prec/ 
--
foreign import ccall "acb_hypgeom.h acb_hypgeom_pfq_series_sum_rs"
  acb_hypgeom_pfq_series_sum_rs :: Ptr CAcbPoly -> Ptr CAcbPoly -> Ptr (Ptr CAcbPoly) -> CLong -> Ptr (Ptr CAcbPoly) -> CLong -> Ptr CAcbPoly -> CInt -> CLong -> CLong -> CLong -> IO ()

-- | /acb_hypgeom_pfq_series_sum/ /s/ /t/ /a/ /p/ /b/ /q/ /z/ /regularized/ /n/ /len/ /prec/ 
--
-- Computes \(s = \sum_{k=0}^{n-1} T(k)\) and \(t = T(n)\) given parameters
-- and argument that are power series. Does not allow aliasing between
-- input and output variables. We require \(n \ge 0\) and that /len/ is
-- positive.
-- 
-- If /regularized/ is set, the regularized sum is computed, avoiding
-- division by zero at the poles of the gamma function.
-- 
-- The /forward/, /bs/, /rs/ and default versions use forward recurrence,
-- binary splitting, rectangular splitting, and an automatic algorithm
-- choice.
foreign import ccall "acb_hypgeom.h acb_hypgeom_pfq_series_sum"
  acb_hypgeom_pfq_series_sum :: Ptr CAcbPoly -> Ptr CAcbPoly -> Ptr (Ptr CAcbPoly) -> CLong -> Ptr (Ptr CAcbPoly) -> CLong -> Ptr CAcbPoly -> CInt -> CLong -> CLong -> CLong -> IO ()

-- | /acb_hypgeom_pfq_series_direct/ /res/ /a/ /p/ /b/ /q/ /z/ /regularized/ /n/ /len/ /prec/ 
--
-- Computes \({}_pf_{q}(z)\) directly using the defining series, given
-- parameters and argument that are power series. The result is a power
-- series of length /len/. We require that /len/ is positive.
-- 
-- An error bound is computed automatically as a function of the number of
-- terms /n/. If \(n < 0\), the number of terms is chosen automatically.
-- 
-- If /regularized/ is set, the regularized hypergeometric function is
-- computed instead.
foreign import ccall "acb_hypgeom.h acb_hypgeom_pfq_series_direct"
  acb_hypgeom_pfq_series_direct :: Ptr CAcbPoly -> Ptr (Ptr CAcbPoly) -> CLong -> Ptr (Ptr CAcbPoly) -> CLong -> Ptr CAcbPoly -> CInt -> CLong -> CLong -> CLong -> IO ()

-- Asymptotic series -----------------------------------------------------------

-- U(a,b,z) is the confluent hypergeometric function of the second kind
-- with the principal branch cut, and \(U^{*} = z^a U(a,b,z)\). For details
-- about how error bounds are computed, see
-- @algorithms_hypergeometric_asymptotic_confluent@.
--
-- | /acb_hypgeom_u_asymp/ /res/ /a/ /b/ /z/ /n/ /prec/ 
--
-- Sets /res/ to \(U^{*}(a,b,z)\) computed using /n/ terms of the
-- asymptotic series, with a rigorous bound for the error included in the
-- output. We require \(n \ge 0\).
foreign import ccall "acb_hypgeom.h acb_hypgeom_u_asymp"
  acb_hypgeom_u_asymp :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> IO ()

-- | /acb_hypgeom_u_use_asymp/ /z/ /prec/ 
--
-- Heuristically determines whether the asymptotic series can be used to
-- evaluate \(U(a,b,z)\) to /prec/ accurate bits (assuming that /a/ and /b/
-- are small).
foreign import ccall "acb_hypgeom.h acb_hypgeom_u_use_asymp"
  acb_hypgeom_u_use_asymp :: Ptr CAcb -> CLong -> IO CInt

-- Generalized hypergeometric function -----------------------------------------

-- | /acb_hypgeom_pfq/ /res/ /a/ /p/ /b/ /q/ /z/ /regularized/ /prec/ 
--
-- Computes the generalized hypergeometric function \({}_pF_{q}(z)\), or
-- the regularized version if /regularized/ is set.
-- 
-- This function automatically delegates to a specialized implementation
-- when the order (/p/, /q/) is one of (0,0), (1,0), (0,1), (1,1), (2,1).
-- Otherwise, it falls back to direct summation.
-- 
-- While this is a top-level function meant to take care of special cases
-- automatically, it does not generally perform the optimization of
-- deleting parameters that appear in both /a/ and /b/. This can be done
-- ahead of time by the user in applications where duplicate parameters are
-- likely to occur.
foreign import ccall "acb_hypgeom.h acb_hypgeom_pfq"
  acb_hypgeom_pfq :: Ptr CAcbPoly -> Ptr CAcb -> CLong -> Ptr CAcb -> CLong -> Ptr CAcb -> CInt -> CLong -> IO ()

-- Confluent hypergeometric functions ------------------------------------------

-- | /acb_hypgeom_u_1f1_series/ /res/ /a/ /b/ /z/ /len/ /prec/ 
--
-- Computes \(U(a,b,z)\) as a power series truncated to length /len/, given
-- \(a, b, z \in \mathbb{C}[[x]]\). If \(b[0] \in \mathbb{Z}\), it computes
-- one extra derivative and removes the singularity (it is then assumed
-- that \(b[1] \ne 0\)). As currently implemented, the output is
-- indeterminate if \(b\) is nonexact and contains an integer.
foreign import ccall "acb_hypgeom.h acb_hypgeom_u_1f1_series"
  acb_hypgeom_u_1f1_series :: Ptr CAcbPoly -> Ptr CAcbPoly -> Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> CLong -> IO ()

-- | /acb_hypgeom_u_1f1/ /res/ /a/ /b/ /z/ /prec/ 
--
-- Computes \(U(a,b,z)\) as a sum of two convergent hypergeometric series.
-- If \(b \in \mathbb{Z}\), it computes the limit value via
-- @acb_hypgeom_u_1f1_series@. As currently implemented, the output is
-- indeterminate if \(b\) is nonexact and contains an integer.
foreign import ccall "acb_hypgeom.h acb_hypgeom_u_1f1"
  acb_hypgeom_u_1f1 :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_hypgeom_u/ /res/ /a/ /b/ /z/ /prec/ 
--
-- Computes \(U(a,b,z)\) using an automatic algorithm choice. The function
-- @acb_hypgeom_u_asymp@ is used if \(a\) or \(a-b+1\) is a nonpositive
-- integer (in which case the asymptotic series terminates), or if /z/ is
-- sufficiently large. Otherwise @acb_hypgeom_u_1f1@ is used.
foreign import ccall "acb_hypgeom.h acb_hypgeom_u"
  acb_hypgeom_u :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_hypgeom_m_asymp/ /res/ /a/ /b/ /z/ /regularized/ /prec/ 
--
foreign import ccall "acb_hypgeom.h acb_hypgeom_m_asymp"
  acb_hypgeom_m_asymp :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CInt -> CLong -> IO ()

-- | /acb_hypgeom_m_1f1/ /res/ /a/ /b/ /z/ /regularized/ /prec/ 
--
foreign import ccall "acb_hypgeom.h acb_hypgeom_m_1f1"
  acb_hypgeom_m_1f1 :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CInt -> CLong -> IO ()

-- | /acb_hypgeom_m/ /res/ /a/ /b/ /z/ /regularized/ /prec/ 
--
-- Computes the confluent hypergeometric function
-- \(M(a,b,z) = {}_1F_1(a,b,z)\), or
-- \(\mathbf{M}(a,b,z) = \frac{1}{\Gamma(b)} {}_1F_1(a,b,z)\) if
-- /regularized/ is set.
foreign import ccall "acb_hypgeom.h acb_hypgeom_m"
  acb_hypgeom_m :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CInt -> CLong -> IO ()

-- | /acb_hypgeom_1f1/ /res/ /a/ /b/ /z/ /regularized/ /prec/ 
--
-- Alias for @acb_hypgeom_m@.
foreign import ccall "acb_hypgeom.h acb_hypgeom_1f1"
  acb_hypgeom_1f1 :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CInt -> CLong -> IO ()

-- | /acb_hypgeom_0f1_asymp/ /res/ /a/ /z/ /regularized/ /prec/ 
--
foreign import ccall "acb_hypgeom.h acb_hypgeom_0f1_asymp"
  acb_hypgeom_0f1_asymp :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CInt -> CLong -> IO ()

-- | /acb_hypgeom_0f1_direct/ /res/ /a/ /z/ /regularized/ /prec/ 
--
foreign import ccall "acb_hypgeom.h acb_hypgeom_0f1_direct"
  acb_hypgeom_0f1_direct :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CInt -> CLong -> IO ()

-- | /acb_hypgeom_0f1/ /res/ /a/ /z/ /regularized/ /prec/ 
--
-- Computes the confluent hypergeometric function \({}_0F_1(a,z)\), or
-- \(\frac{1}{\Gamma(a)} {}_0F_1(a,z)\) if /regularized/ is set, using
-- asymptotic expansions, direct summation, or an automatic algorithm
-- choice. The /asymp/ version uses the asymptotic expansions of Bessel
-- functions, together with the connection formulas
-- 
-- \[`\]
-- \[\frac{{}_0F_1(a,z)}{\Gamma(a)} = (-z)^{(1-a)/2} J_{a-1}(2 \sqrt{-z}) =
--                                  z^{(1-a)/2} I_{a-1}(2 \sqrt{z}).\]
-- 
-- The Bessel-/J/ function is used in the left half-plane and the
-- Bessel-/I/ function is used in the right half-plane, to avoid loss of
-- accuracy due to evaluating the square root on the branch cut.
foreign import ccall "acb_hypgeom.h acb_hypgeom_0f1"
  acb_hypgeom_0f1 :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CInt -> CLong -> IO ()

-- Error functions and Fresnel integrals ---------------------------------------

-- | /acb_hypgeom_erf_propagated_error/ /re/ /im/ /z/ 
--
-- Sets /re/ and /im/ to upper bounds for the error in the real and
-- imaginary part resulting from approximating the error function of /z/ by
-- the error function evaluated at the midpoint of /z/. Uses the first
-- derivative.
foreign import ccall "acb_hypgeom.h acb_hypgeom_erf_propagated_error"
  acb_hypgeom_erf_propagated_error :: Ptr CMag -> Ptr CMag -> Ptr CAcb -> IO ()

-- | /acb_hypgeom_erf_1f1a/ /res/ /z/ /prec/ 
--
foreign import ccall "acb_hypgeom.h acb_hypgeom_erf_1f1a"
  acb_hypgeom_erf_1f1a :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_hypgeom_erf_1f1b/ /res/ /z/ /prec/ 
--
foreign import ccall "acb_hypgeom.h acb_hypgeom_erf_1f1b"
  acb_hypgeom_erf_1f1b :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_hypgeom_erf_asymp/ /res/ /z/ /complementary/ /prec/ /prec2/ 
--
-- Computes the error function respectively using
-- 
-- \[`\]
-- \[\operatorname{erf}(z) &= \frac{2z}{\sqrt{\pi}}
--     {}_1F_1(\tfrac{1}{2}, \tfrac{3}{2}, -z^2)\]
-- \[\operatorname{erf}(z) &= \frac{2z e^{-z^2}}{\sqrt{\pi}}
--     {}_1F_1(1, \tfrac{3}{2}, z^2)\]
-- \[\operatorname{erf}(z) &= \frac{z}{\sqrt{z^2}}
--     \left(1 - \frac{e^{-z^2}}{\sqrt{\pi}}
--     U(\tfrac{1}{2}, \tfrac{1}{2}, z^2)\right) =
--     \frac{z}{\sqrt{z^2}} - \frac{e^{-z^2}}{z \sqrt{\pi}}
--     U^{*}(\tfrac{1}{2}, \tfrac{1}{2}, z^2).\]
-- 
-- The /asymp/ version takes a second precision to use for the /U/ term. It
-- also takes an extra flag /complementary/, computing the complementary
-- error function if set.
foreign import ccall "acb_hypgeom.h acb_hypgeom_erf_asymp"
  acb_hypgeom_erf_asymp :: Ptr CAcb -> Ptr CAcb -> CInt -> CLong -> CLong -> IO ()

-- | /acb_hypgeom_erf/ /res/ /z/ /prec/ 
--
-- Computes the error function using an automatic algorithm choice. If /z/
-- is too small to use the asymptotic expansion, a working precision
-- sufficient to circumvent cancellation in the hypergeometric series is
-- determined automatically, and a bound for the propagated error is
-- computed with @acb_hypgeom_erf_propagated_error@.
foreign import ccall "acb_hypgeom.h acb_hypgeom_erf"
  acb_hypgeom_erf :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /_acb_hypgeom_erf_series/ /res/ /z/ /zlen/ /len/ /prec/ 
--
foreign import ccall "acb_hypgeom.h _acb_hypgeom_erf_series"
  _acb_hypgeom_erf_series :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> CLong -> IO ()

-- | /acb_hypgeom_erf_series/ /res/ /z/ /len/ /prec/ 
--
-- Computes the error function of the power series /z/, truncated to length
-- /len/.
foreign import ccall "acb_hypgeom.h acb_hypgeom_erf_series"
  acb_hypgeom_erf_series :: Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> CLong -> IO ()

-- | /acb_hypgeom_erfc/ /res/ /z/ /prec/ 
--
-- Computes the complementary error function
-- \(\operatorname{erfc}(z) = 1 - \operatorname{erf}(z)\). This function
-- avoids catastrophic cancellation for large positive /z/.
foreign import ccall "acb_hypgeom.h acb_hypgeom_erfc"
  acb_hypgeom_erfc :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /_acb_hypgeom_erfc_series/ /res/ /z/ /zlen/ /len/ /prec/ 
--
foreign import ccall "acb_hypgeom.h _acb_hypgeom_erfc_series"
  _acb_hypgeom_erfc_series :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> CLong -> IO ()

-- | /acb_hypgeom_erfc_series/ /res/ /z/ /len/ /prec/ 
--
-- Computes the complementary error function of the power series /z/,
-- truncated to length /len/.
foreign import ccall "acb_hypgeom.h acb_hypgeom_erfc_series"
  acb_hypgeom_erfc_series :: Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> CLong -> IO ()

-- | /acb_hypgeom_erfi/ /res/ /z/ /prec/ 
--
-- Computes the imaginary error function
-- \(\operatorname{erfi}(z) = -i\operatorname{erf}(iz)\). This is a trivial
-- wrapper of @acb_hypgeom_erf@.
foreign import ccall "acb_hypgeom.h acb_hypgeom_erfi"
  acb_hypgeom_erfi :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /_acb_hypgeom_erfi_series/ /res/ /z/ /zlen/ /len/ /prec/ 
--
foreign import ccall "acb_hypgeom.h _acb_hypgeom_erfi_series"
  _acb_hypgeom_erfi_series :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> CLong -> IO ()

-- | /acb_hypgeom_erfi_series/ /res/ /z/ /len/ /prec/ 
--
-- Computes the imaginary error function of the power series /z/, truncated
-- to length /len/.
foreign import ccall "acb_hypgeom.h acb_hypgeom_erfi_series"
  acb_hypgeom_erfi_series :: Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> CLong -> IO ()

-- | /acb_hypgeom_fresnel/ /res1/ /res2/ /z/ /normalized/ /prec/ 
--
-- Sets /res1/ to the Fresnel sine integral \(S(z)\) and /res2/ to the
-- Fresnel cosine integral \(C(z)\). Optionally, just a single function can
-- be computed by passing /NULL/ as the other output variable. The
-- definition \(S(z) = \int_0^z \sin(t^2) dt\) is used if /normalized/ is
-- 0, and \(S(z) = \int_0^z \sin(\tfrac{1}{2} \pi t^2) dt\) is used if
-- /normalized/ is 1 (the latter is the Abramowitz & Stegun convention).
-- \(C(z)\) is defined analogously.
foreign import ccall "acb_hypgeom.h acb_hypgeom_fresnel"
  acb_hypgeom_fresnel :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CInt -> CLong -> IO ()

-- | /_acb_hypgeom_fresnel_series/ /res1/ /res2/ /z/ /zlen/ /normalized/ /len/ /prec/ 
--
foreign import ccall "acb_hypgeom.h _acb_hypgeom_fresnel_series"
  _acb_hypgeom_fresnel_series :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> CInt -> CLong -> CLong -> IO ()

-- | /acb_hypgeom_fresnel_series/ /res1/ /res2/ /z/ /normalized/ /len/ /prec/ 
--
-- Sets /res1/ to the Fresnel sine integral and /res2/ to the Fresnel
-- cosine integral of the power series /z/, truncated to length /len/.
-- Optionally, just a single function can be computed by passing /NULL/ as
-- the other output variable.
foreign import ccall "acb_hypgeom.h acb_hypgeom_fresnel_series"
  acb_hypgeom_fresnel_series :: Ptr CAcbPoly -> Ptr CAcbPoly -> Ptr CAcbPoly -> CInt -> CLong -> CLong -> IO ()

-- Bessel functions ------------------------------------------------------------

-- | /acb_hypgeom_bessel_j_asymp/ /res/ /nu/ /z/ /prec/ 
--
-- Computes the Bessel function of the first kind via
-- @acb_hypgeom_u_asymp@. For all complex \(\nu, z\), we have
-- 
-- \[`\]
-- \[J_{\nu}(z) = \frac{z^{\nu}}{2^{\nu} e^{iz} \Gamma(\nu+1)}
--     {}_1F_1(\nu+\tfrac{1}{2}, 2\nu+1, 2iz) = A_{+} B_{+} + A_{-} B_{-}\]
-- 
-- where
-- 
-- \[`\]
-- \[A_{\pm} = z^{\nu} (z^2)^{-\tfrac{1}{2}-\nu} (\mp i z)^{\tfrac{1}{2}+\nu} (2 \pi)^{-1/2} = (\pm iz)^{-1/2-\nu} z^{\nu} (2 \pi)^{-1/2}\]
-- 
-- \[`\]
-- \[B_{\pm} = e^{\pm i z} U^{*}(\nu+\tfrac{1}{2}, 2\nu+1, \mp 2iz).\]
-- 
-- Nicer representations of the factors \(A_{\pm}\) can be given depending
-- conditionally on the parameters. If
-- \(\nu + \tfrac{1}{2} = n \in \mathbb{Z}\), we have
-- \(A_{\pm} = (\pm i)^{n} (2 \pi z)^{-1/2}\). And if
-- \(\operatorname{Re}(z) > 0\), we have
-- \(A_{\pm} = \exp(\mp i [(2\nu+1)/4] \pi) (2 \pi z)^{-1/2}\).
foreign import ccall "acb_hypgeom.h acb_hypgeom_bessel_j_asymp"
  acb_hypgeom_bessel_j_asymp :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_hypgeom_bessel_j_0f1/ /res/ /nu/ /z/ /prec/ 
--
-- Computes the Bessel function of the first kind from
-- 
-- \[`\]
-- \[J_{\nu}(z) = \frac{1}{\Gamma(\nu+1)} \left(\frac{z}{2}\right)^{\nu}
--              {}_0F_1\left(\nu+1, -\frac{z^2}{4}\right).\]
foreign import ccall "acb_hypgeom.h acb_hypgeom_bessel_j_0f1"
  acb_hypgeom_bessel_j_0f1 :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_hypgeom_bessel_j/ /res/ /nu/ /z/ /prec/ 
--
-- Computes the Bessel function of the first kind \(J_{\nu}(z)\) using an
-- automatic algorithm choice.
foreign import ccall "acb_hypgeom.h acb_hypgeom_bessel_j"
  acb_hypgeom_bessel_j :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_hypgeom_bessel_y/ /res/ /nu/ /z/ /prec/ 
--
-- Computes the Bessel function of the second kind \(Y_{\nu}(z)\) from the
-- formula
-- 
-- \[`\]
-- \[Y_{\nu}(z) = \frac{\cos(\nu \pi) J_{\nu}(z) - J_{-\nu}(z)}{\sin(\nu \pi)}\]
-- 
-- unless \(\nu = n\) is an integer in which case the limit value
-- 
-- \[`\]
-- \[Y_n(z) = -\frac{2}{\pi} \left( i^n K_n(iz) +
--     \left[\log(iz)-\log(z)\right] J_n(z) \right)\]
-- 
-- is computed. As currently implemented, the output is indeterminate if
-- \(\nu\) is nonexact and contains an integer.
foreign import ccall "acb_hypgeom.h acb_hypgeom_bessel_y"
  acb_hypgeom_bessel_y :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_hypgeom_bessel_jy/ /res1/ /res2/ /nu/ /z/ /prec/ 
--
-- Sets /res1/ to \(J_{\nu}(z)\) and /res2/ to \(Y_{\nu}(z)\), computed
-- simultaneously. From these values, the user can easily construct the
-- Bessel functions of the third kind (Hankel functions)
-- \(H_{\nu}^{(1)}(z), H_{\nu}^{(2)}(z) = J_{\nu}(z) \pm i Y_{\nu}(z)\).
foreign import ccall "acb_hypgeom.h acb_hypgeom_bessel_jy"
  acb_hypgeom_bessel_jy :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- Modified Bessel functions ---------------------------------------------------

-- | /acb_hypgeom_bessel_i_asymp/ /res/ /nu/ /z/ /scaled/ /prec/ 
--
foreign import ccall "acb_hypgeom.h acb_hypgeom_bessel_i_asymp"
  acb_hypgeom_bessel_i_asymp :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CInt -> CLong -> IO ()

-- | /acb_hypgeom_bessel_i_0f1/ /res/ /nu/ /z/ /scaled/ /prec/ 
--
foreign import ccall "acb_hypgeom.h acb_hypgeom_bessel_i_0f1"
  acb_hypgeom_bessel_i_0f1 :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CInt -> CLong -> IO ()

-- | /acb_hypgeom_bessel_i/ /res/ /nu/ /z/ /prec/ 
--
foreign import ccall "acb_hypgeom.h acb_hypgeom_bessel_i"
  acb_hypgeom_bessel_i :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_hypgeom_bessel_i_scaled/ /res/ /nu/ /z/ /prec/ 
--
-- Computes the modified Bessel function of the first kind
-- \(I_{\nu}(z) = z^{\nu} (iz)^{-\nu} J_{\nu}(iz)\) respectively using
-- asymptotic series (see @acb_hypgeom_bessel_j_asymp@), the convergent
-- series
-- 
-- \[`\]
-- \[I_{\nu}(z) = \frac{1}{\Gamma(\nu+1)} \left(\frac{z}{2}\right)^{\nu}
--              {}_0F_1\left(\nu+1, \frac{z^2}{4}\right),\]
-- 
-- or an automatic algorithm choice.
-- 
-- The /scaled/ version computes the function \(e^{-z} I_{\nu}(z)\). The
-- /asymp/ and /0f1/ functions implement both variants and allow choosing
-- with a flag.
foreign import ccall "acb_hypgeom.h acb_hypgeom_bessel_i_scaled"
  acb_hypgeom_bessel_i_scaled :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_hypgeom_bessel_k_asymp/ /res/ /nu/ /z/ /scaled/ /prec/ 
--
-- Computes the modified Bessel function of the second kind via via
-- @acb_hypgeom_u_asymp@. For all \(\nu\) and all \(z \ne 0\), we have
-- 
-- \[`\]
-- \[K_{\nu}(z) = \left(\frac{2z}{\pi}\right)^{-1/2} e^{-z}
--     U^{*}(\nu+\tfrac{1}{2}, 2\nu+1, 2z).\]
-- 
-- If /scaled/ is set, computes the function \(e^{z} K_{\nu}(z)\).
foreign import ccall "acb_hypgeom.h acb_hypgeom_bessel_k_asymp"
  acb_hypgeom_bessel_k_asymp :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CInt -> CLong -> IO ()

-- | /acb_hypgeom_bessel_k_0f1_series/ /res/ /nu/ /z/ /scaled/ /len/ /prec/ 
--
-- Computes the modified Bessel function of the second kind \(K_{\nu}(z)\)
-- as a power series truncated to length /len/, given
-- \(\nu, z \in \mathbb{C}[[x]]\). Uses the formula
-- 
-- \[`\]
-- \[K_{\nu}(z) = \frac{1}{2} \frac{\pi}{\sin(\pi \nu)} \left[
--             \left(\frac{z}{2}\right)^{-\nu}
--                 {}_0{\widetilde F}_1\left(1-\nu, \frac{z^2}{4}\right)
--              -
--              \left(\frac{z}{2}\right)^{\nu}
--                  {}_0{\widetilde F}_1\left(1+\nu, \frac{z^2}{4}\right)
--             \right].\]
-- 
-- If \(\nu[0] \in \mathbb{Z}\), it computes one extra derivative and
-- removes the singularity (it is then assumed that \(\nu[1] \ne 0\)). As
-- currently implemented, the output is indeterminate if \(\nu[0]\) is
-- nonexact and contains an integer.
-- 
-- If /scaled/ is set, computes the function \(e^{z} K_{\nu}(z)\).
foreign import ccall "acb_hypgeom.h acb_hypgeom_bessel_k_0f1_series"
  acb_hypgeom_bessel_k_0f1_series :: Ptr CAcbPoly -> Ptr CAcbPoly -> Ptr CAcbPoly -> CInt -> CLong -> CLong -> IO ()

-- | /acb_hypgeom_bessel_k_0f1/ /res/ /nu/ /z/ /scaled/ /prec/ 
--
-- Computes the modified Bessel function of the second kind from
-- 
-- \[`\]
-- \[K_{\nu}(z) = \frac{1}{2} \left[
--             \left(\frac{z}{2}\right)^{-\nu}
--                 \Gamma(\nu)
--                 {}_0F_1\left(1-\nu, \frac{z^2}{4}\right)
--              -
--              \left(\frac{z}{2}\right)^{\nu}
--                  \frac{\pi}{\nu \sin(\pi \nu) \Gamma(\nu)}
--                  {}_0F_1\left(\nu+1, \frac{z^2}{4}\right)
--             \right]\]
-- 
-- if \(\nu \notin \mathbb{Z}\). If \(\nu \in \mathbb{Z}\), it computes the
-- limit value via @acb_hypgeom_bessel_k_0f1_series@. As currently
-- implemented, the output is indeterminate if \(\nu\) is nonexact and
-- contains an integer.
-- 
-- If /scaled/ is set, computes the function \(e^{z} K_{\nu}(z)\).
foreign import ccall "acb_hypgeom.h acb_hypgeom_bessel_k_0f1"
  acb_hypgeom_bessel_k_0f1 :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CInt -> CLong -> IO ()

-- | /acb_hypgeom_bessel_k/ /res/ /nu/ /z/ /prec/ 
--
-- Computes the modified Bessel function of the second kind \(K_{\nu}(z)\)
-- using an automatic algorithm choice.
foreign import ccall "acb_hypgeom.h acb_hypgeom_bessel_k"
  acb_hypgeom_bessel_k :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_hypgeom_bessel_k_scaled/ /res/ /nu/ /z/ /prec/ 
--
-- Computes the function \(e^{z} K_{\nu}(z)\).
foreign import ccall "acb_hypgeom.h acb_hypgeom_bessel_k_scaled"
  acb_hypgeom_bessel_k_scaled :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- Airy functions --------------------------------------------------------------

-- The Airy functions are linearly independent solutions of the
-- differential equation \(y'' - zy = 0\). All solutions are entire
-- functions. The standard solutions are denoted
-- \(\operatorname{Ai}(z), \operatorname{Bi}(z)\). For negative /z/, both
-- functions are oscillatory. For positive /z/, the first function
-- decreases exponentially while the second increases exponentially.
--
-- The Airy functions can be expressed in terms of Bessel functions of
-- fractional order, but this is inconvenient since such formulas only hold
-- piecewise (due to the Stokes phenomenon). Computation of the Airy
-- functions can also be optimized more than Bessel functions in general.
-- We therefore provide a dedicated interface for evaluating Airy
-- functions.
--
-- The following methods optionally compute (operatorname{Ai}(z),
-- operatorname{Ai}\'(z), operatorname{Bi}(z), operatorname{Bi}\'(z))
-- simultaneously. Any of the four function values can be omitted by
-- passing /NULL/ for the unwanted output variables, speeding up the
-- evaluation.
--
-- | /acb_hypgeom_airy_direct/ /ai/ /ai_prime/ /bi/ /bi_prime/ /z/ /n/ /prec/ 
--
-- Computes the Airy functions using direct series expansions truncated at
-- /n/ terms. Error bounds are included in the output.
foreign import ccall "acb_hypgeom.h acb_hypgeom_airy_direct"
  acb_hypgeom_airy_direct :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> IO ()

-- | /acb_hypgeom_airy_asymp/ /ai/ /ai_prime/ /bi/ /bi_prime/ /z/ /n/ /prec/ 
--
-- Computes the Airy functions using asymptotic expansions truncated at /n/
-- terms. Error bounds are included in the output. For details about how
-- the error bounds are computed, see
-- @algorithms_hypergeometric_asymptotic_airy@.
foreign import ccall "acb_hypgeom.h acb_hypgeom_airy_asymp"
  acb_hypgeom_airy_asymp :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> IO ()

-- | /acb_hypgeom_airy_bound/ /ai/ /ai_prime/ /bi/ /bi_prime/ /z/ 
--
-- Computes bounds for the Airy functions using first-order asymptotic
-- expansions together with error bounds. This function uses some shortcuts
-- to make it slightly faster than calling @acb_hypgeom_airy_asymp@ with
-- \(n = 1\).
foreign import ccall "acb_hypgeom.h acb_hypgeom_airy_bound"
  acb_hypgeom_airy_bound :: Ptr CMag -> Ptr CMag -> Ptr CMag -> Ptr CMag -> Ptr CAcb -> IO ()

-- | /acb_hypgeom_airy/ /ai/ /ai_prime/ /bi/ /bi_prime/ /z/ /prec/ 
--
-- Computes Airy functions using an automatic algorithm choice.
-- 
-- We use @acb_hypgeom_airy_asymp@ whenever this gives full accuracy and
-- @acb_hypgeom_airy_direct@ otherwise. In the latter case, we first use
-- hardware double precision arithmetic to determine an accurate estimate
-- of the working precision needed to compute the Airy functions accurately
-- for given /z/. This estimate is obtained by comparing the leading-order
-- asymptotic estimate of the Airy functions with the magnitude of the
-- largest term in the power series. The estimate is generic in the sense
-- that it does not take into account vanishing near the roots of the
-- functions. We subsequently evaluate the power series at the midpoint of
-- /z/ and bound the propagated error using derivatives. Derivatives are
-- bounded using @acb_hypgeom_airy_bound@.
foreign import ccall "acb_hypgeom.h acb_hypgeom_airy"
  acb_hypgeom_airy :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_hypgeom_airy_jet/ /ai/ /bi/ /z/ /len/ /prec/ 
--
-- Writes to /ai/ and /bi/ the respective Taylor expansions of the Airy
-- functions at the point /z/, truncated to length /len/. Either of the
-- outputs can be /NULL/ to avoid computing that function. The variable /z/
-- is not allowed to be aliased with the outputs. To simplify the
-- implementation, this method does not compute the series expansions of
-- the primed versions directly; these are easily obtained by computing one
-- extra coefficient and differentiating the output with
-- @_acb_poly_derivative@.
foreign import ccall "acb_hypgeom.h acb_hypgeom_airy_jet"
  acb_hypgeom_airy_jet :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> IO ()

-- | /_acb_hypgeom_airy_series/ /ai/ /ai_prime/ /bi/ /bi_prime/ /z/ /zlen/ /len/ /prec/ 
--
foreign import ccall "acb_hypgeom.h _acb_hypgeom_airy_series"
  _acb_hypgeom_airy_series :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> CLong -> IO ()

-- | /acb_hypgeom_airy_series/ /ai/ /ai_prime/ /bi/ /bi_prime/ /z/ /len/ /prec/ 
--
-- Computes the Airy functions evaluated at the power series /z/, truncated
-- to length /len/. As with the other Airy methods, any of the outputs can
-- be /NULL/.
foreign import ccall "acb_hypgeom.h acb_hypgeom_airy_series"
  acb_hypgeom_airy_series :: Ptr CAcbPoly -> Ptr CAcbPoly -> Ptr CAcbPoly -> Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> CLong -> IO ()

-- Coulomb wave functions ------------------------------------------------------

-- Coulomb wave functions are solutions of the Coulomb wave equation
--
-- \[`\]
-- \[y'' + \left(1 - \frac{2 \eta}{z} - \frac{\ell(\ell+1)}{z^2}\right) y = 0\]
--
-- which is the radial Schrödinger equation for a charged particle in a
-- Coulomb potential \(1/z\), where \(\ell\) is the orbital angular
-- momentum and eta is the Sommerfeld parameter. The standard solutions are
-- named \(F_{\ell}(\eta,z)\) (regular at the origin \(z = 0\)) and
-- \(G_{\ell}(\eta,z)\) (irregular at the origin). The irregular solutions
-- H^{pm}_{ell}(eta,z) = G_{ell}(eta,z) pm i F_{ell}(eta,z) are also used.
--
-- Coulomb wave functions are special cases of confluent hypergeometric
-- functions. The normalization constants and connection formulas are
-- discussed in < [DYF1999]>, < [Gas2018]>, < [Mic2007]> and chapter 33 in
-- < [NIST2012]>. In this implementation, we define the analytic
-- continuations of all the functions so that the branch cut with respect
-- to /z/ is placed on the negative real axis. Precise definitions are
-- given in <http://fungrim.org/topic/Coulomb_wave_functions/>
--
-- The following methods optionally compute F_{ell}(eta,z), G_{ell}(eta,z),
-- H^{+}_{ell}(eta,z), H^{-}_{ell}(eta,z) simultaneously. Any of the four
-- function values can be omitted by passing /NULL/ for the unwanted output
-- variables. The redundant functions \(H^{\pm}\) are provided explicitly
-- since taking the linear combination of /F/ and /G/ suffers from
-- cancellation in parts of the complex plane.
--
-- | /acb_hypgeom_coulomb/ /F/ /G/ /Hpos/ /Hneg/ /l/ /eta/ /z/ /prec/ 
--
-- Writes to /F/, /G/, /Hpos/, /Hneg/ the values of the respective Coulomb
-- wave functions. Any of the outputs can be /NULL/.
foreign import ccall "acb_hypgeom.h acb_hypgeom_coulomb"
  acb_hypgeom_coulomb :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_hypgeom_coulomb_jet/ /F/ /G/ /Hpos/ /Hneg/ /l/ /eta/ /z/ /len/ /prec/ 
--
-- Writes to /F/, /G/, /Hpos/, /Hneg/ the respective Taylor expansions of
-- the Coulomb wave functions at the point /z/, truncated to length /len/.
-- Any of the outputs can be /NULL/.
foreign import ccall "acb_hypgeom.h acb_hypgeom_coulomb_jet"
  acb_hypgeom_coulomb_jet :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> IO ()

-- | /_acb_hypgeom_coulomb_series/ /F/ /G/ /Hpos/ /Hneg/ /l/ /eta/ /z/ /zlen/ /len/ /prec/ 
--
foreign import ccall "acb_hypgeom.h _acb_hypgeom_coulomb_series"
  _acb_hypgeom_coulomb_series :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> CLong -> IO ()

-- | /acb_hypgeom_coulomb_series/ /F/ /G/ /Hpos/ /Hneg/ /l/ /eta/ /z/ /len/ /prec/ 
--
-- Computes the Coulomb wave functions evaluated at the power series /z/,
-- truncated to length /len/. Any of the outputs can be /NULL/.
foreign import ccall "acb_hypgeom.h acb_hypgeom_coulomb_series"
  acb_hypgeom_coulomb_series :: Ptr CAcbPoly -> Ptr CAcbPoly -> Ptr CAcbPoly -> Ptr CAcbPoly -> Ptr CAcb -> Ptr CAcb -> Ptr CAcbPoly -> CLong -> CLong -> IO ()

-- Incomplete gamma and beta functions -----------------------------------------

-- | /acb_hypgeom_gamma_upper_asymp/ /res/ /s/ /z/ /regularized/ /prec/ 
--
foreign import ccall "acb_hypgeom.h acb_hypgeom_gamma_upper_asymp"
  acb_hypgeom_gamma_upper_asymp :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CInt -> CLong -> IO ()

-- | /acb_hypgeom_gamma_upper_1f1a/ /res/ /s/ /z/ /regularized/ /prec/ 
--
foreign import ccall "acb_hypgeom.h acb_hypgeom_gamma_upper_1f1a"
  acb_hypgeom_gamma_upper_1f1a :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CInt -> CLong -> IO ()

-- | /acb_hypgeom_gamma_upper_1f1b/ /res/ /s/ /z/ /regularized/ /prec/ 
--
foreign import ccall "acb_hypgeom.h acb_hypgeom_gamma_upper_1f1b"
  acb_hypgeom_gamma_upper_1f1b :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CInt -> CLong -> IO ()

-- | /acb_hypgeom_gamma_upper_singular/ /res/ /s/ /z/ /regularized/ /prec/ 
--
foreign import ccall "acb_hypgeom.h acb_hypgeom_gamma_upper_singular"
  acb_hypgeom_gamma_upper_singular :: Ptr CAcb -> CLong -> Ptr CAcb -> CInt -> CLong -> IO ()

-- | /acb_hypgeom_gamma_upper/ /res/ /s/ /z/ /regularized/ /prec/ 
--
-- If /regularized/ is 0, computes the upper incomplete gamma function
-- \(\Gamma(s,z)\).
-- 
-- If /regularized/ is 1, computes the regularized upper incomplete gamma
-- function \(Q(s,z) = \Gamma(s,z) / \Gamma(s)\).
-- 
-- If /regularized/ is 2, computes the generalized exponential integral
-- \(z^{-s} \Gamma(s,z) = E_{1-s}(z)\) instead (this option is mainly
-- intended for internal use; @acb_hypgeom_expint@ is the intended
-- interface for computing the exponential integral).
-- 
-- The different methods respectively implement the formulas
-- 
-- \[`\]
-- \[\Gamma(s,z) = e^{-z} U(1-s,1-s,z)\]
-- 
-- \[`\]
-- \[\Gamma(s,z) = \Gamma(s) - \frac{z^s}{s} {}_1F_1(s, s+1, -z)\]
-- 
-- \[`\]
-- \[\Gamma(s,z) = \Gamma(s) - \frac{z^s e^{-z}}{s} {}_1F_1(1, s+1, z)\]
-- 
-- \[`\]
-- \[\Gamma(s,z) = \frac{(-1)^n}{n!} (\psi(n+1) - \log(z))
--             + \frac{(-1)^n}{(n+1)!} z \, {}_2F_2(1,1,2,2+n,-z)
--             - z^{-n} \sum_{k=0}^{n-1} \frac{(-z)^k}{(k-n) k!},
--             \quad n = -s \in \mathbb{Z}_{\ge 0}\]
-- 
-- and an automatic algorithm choice. The automatic version also handles
-- other special input such as \(z = 0\) and \(s = 1, 2, 3\). The
-- /singular/ version evaluates the finite sum directly and therefore
-- assumes that /s/ is not too large.
foreign import ccall "acb_hypgeom.h acb_hypgeom_gamma_upper"
  acb_hypgeom_gamma_upper :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CInt -> CLong -> IO ()

-- | /_acb_hypgeom_gamma_upper_series/ /res/ /s/ /z/ /zlen/ /regularized/ /n/ /prec/ 
--
foreign import ccall "acb_hypgeom.h _acb_hypgeom_gamma_upper_series"
  _acb_hypgeom_gamma_upper_series :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> CInt -> CLong -> CLong -> IO ()

-- | /acb_hypgeom_gamma_upper_series/ /res/ /s/ /z/ /regularized/ /n/ /prec/ 
--
-- Sets /res/ to an upper incomplete gamma function where /s/ is a constant
-- and /z/ is a power series, truncated to length /n/. The /regularized/
-- argument has the same interpretation as in @acb_hypgeom_gamma_upper@.
foreign import ccall "acb_hypgeom.h acb_hypgeom_gamma_upper_series"
  acb_hypgeom_gamma_upper_series :: Ptr CAcbPoly -> Ptr CAcb -> Ptr CAcbPoly -> CInt -> CLong -> CLong -> IO ()

-- | /acb_hypgeom_gamma_lower/ /res/ /s/ /z/ /regularized/ /prec/ 
--
-- If /regularized/ is 0, computes the lower incomplete gamma function
-- \(\gamma(s,z) = \frac{z^s}{s} {}_1F_1(s, s+1, -z)\).
-- 
-- If /regularized/ is 1, computes the regularized lower incomplete gamma
-- function \(P(s,z) = \gamma(s,z) / \Gamma(s)\).
-- 
-- If /regularized/ is 2, computes a further regularized lower incomplete
-- gamma function \(\gamma^{*}(s,z) = z^{-s} P(s,z)\).
foreign import ccall "acb_hypgeom.h acb_hypgeom_gamma_lower"
  acb_hypgeom_gamma_lower :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CInt -> CLong -> IO ()

-- | /_acb_hypgeom_gamma_lower_series/ /res/ /s/ /z/ /zlen/ /regularized/ /n/ /prec/ 
--
foreign import ccall "acb_hypgeom.h _acb_hypgeom_gamma_lower_series"
  _acb_hypgeom_gamma_lower_series :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> CInt -> CLong -> CLong -> IO ()

-- | /acb_hypgeom_gamma_lower_series/ /res/ /s/ /z/ /regularized/ /n/ /prec/ 
--
-- Sets /res/ to an lower incomplete gamma function where /s/ is a constant
-- and /z/ is a power series, truncated to length /n/. The /regularized/
-- argument has the same interpretation as in @acb_hypgeom_gamma_lower@.
foreign import ccall "acb_hypgeom.h acb_hypgeom_gamma_lower_series"
  acb_hypgeom_gamma_lower_series :: Ptr CAcbPoly -> Ptr CAcb -> Ptr CAcbPoly -> CInt -> CLong -> CLong -> IO ()

-- | /acb_hypgeom_beta_lower/ /res/ /a/ /b/ /z/ /regularized/ /prec/ 
--
-- Computes the (lower) incomplete beta function, defined by
-- \(B(a,b;z) = \int_0^z t^{a-1} (1-t)^{b-1}\), optionally the regularized
-- incomplete beta function \(I(a,b;z) = B(a,b;z) / B(a,b;1)\).
-- 
-- In general, the integral must be interpreted using analytic
-- continuation. The precise definitions for all parameter values are
-- 
-- \[`\]
-- \[B(a,b;z) = \frac{z^a}{a} {}_2F_1(a, 1-b, a+1, z)\]
-- 
-- \[`\]
-- \[I(a,b;z) = \frac{\Gamma(a+b)}{\Gamma(b)} z^a {}_2{\widetilde F}_1(a, 1-b, a+1, z).\]
-- 
-- Note that both functions with this definition are undefined for
-- nonpositive integer /a/, and /I/ is undefined for nonpositive integer
-- \(a + b\).
foreign import ccall "acb_hypgeom.h acb_hypgeom_beta_lower"
  acb_hypgeom_beta_lower :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CInt -> CLong -> IO ()

-- | /_acb_hypgeom_beta_lower_series/ /res/ /a/ /b/ /z/ /zlen/ /regularized/ /n/ /prec/ 
--
foreign import ccall "acb_hypgeom.h _acb_hypgeom_beta_lower_series"
  _acb_hypgeom_beta_lower_series :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> CInt -> CLong -> CLong -> IO ()

-- | /acb_hypgeom_beta_lower_series/ /res/ /a/ /b/ /z/ /regularized/ /n/ /prec/ 
--
-- Sets /res/ to the lower incomplete beta function \(B(a,b;z)\)
-- (optionally the regularized version \(I(a,b;z)\)) where /a/ and /b/ are
-- constants and /z/ is a power series, truncating the result to length
-- /n/. The underscore method requires positive lengths and does not
-- support aliasing.
foreign import ccall "acb_hypgeom.h acb_hypgeom_beta_lower_series"
  acb_hypgeom_beta_lower_series :: Ptr CAcbPoly -> Ptr CAcb -> Ptr CAcb -> Ptr CAcbPoly -> CInt -> CLong -> CLong -> IO ()

-- Exponential and trigonometric integrals -------------------------------------

-- The branch cut conventions of the following functions match Mathematica.
--
-- | /acb_hypgeom_expint/ /res/ /s/ /z/ /prec/ 
--
-- Computes the generalized exponential integral \(E_s(z)\). This is a
-- trivial wrapper of @acb_hypgeom_gamma_upper@.
foreign import ccall "acb_hypgeom.h acb_hypgeom_expint"
  acb_hypgeom_expint :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_hypgeom_ei_asymp/ /res/ /z/ /prec/ 
--
foreign import ccall "acb_hypgeom.h acb_hypgeom_ei_asymp"
  acb_hypgeom_ei_asymp :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_hypgeom_ei_2f2/ /res/ /z/ /prec/ 
--
foreign import ccall "acb_hypgeom.h acb_hypgeom_ei_2f2"
  acb_hypgeom_ei_2f2 :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_hypgeom_ei/ /res/ /z/ /prec/ 
--
-- Computes the exponential integral \(\operatorname{Ei}(z)\), respectively
-- using
-- 
-- \[`\]
-- \[\operatorname{Ei}(z) = -e^z U(1,1,-z) - \log(-z)
--     + \frac{1}{2} \left(\log(z) - \log\left(\frac{1}{z}\right) \right)\]
-- 
-- \[`\]
-- \[\operatorname{Ei}(z) = z {}_2F_2(1, 1; 2, 2; z) + \gamma
--     + \frac{1}{2} \left(\log(z) - \log\left(\frac{1}{z}\right) \right)\]
-- 
-- and an automatic algorithm choice.
foreign import ccall "acb_hypgeom.h acb_hypgeom_ei"
  acb_hypgeom_ei :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /_acb_hypgeom_ei_series/ /res/ /z/ /zlen/ /len/ /prec/ 
--
foreign import ccall "acb_hypgeom.h _acb_hypgeom_ei_series"
  _acb_hypgeom_ei_series :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> CLong -> IO ()

-- | /acb_hypgeom_ei_series/ /res/ /z/ /len/ /prec/ 
--
-- Computes the exponential integral of the power series /z/, truncated to
-- length /len/.
foreign import ccall "acb_hypgeom.h acb_hypgeom_ei_series"
  acb_hypgeom_ei_series :: Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> CLong -> IO ()

-- | /acb_hypgeom_si_asymp/ /res/ /z/ /prec/ 
--
foreign import ccall "acb_hypgeom.h acb_hypgeom_si_asymp"
  acb_hypgeom_si_asymp :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_hypgeom_si_1f2/ /res/ /z/ /prec/ 
--
foreign import ccall "acb_hypgeom.h acb_hypgeom_si_1f2"
  acb_hypgeom_si_1f2 :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_hypgeom_si/ /res/ /z/ /prec/ 
--
-- Computes the sine integral \(\operatorname{Si}(z)\), respectively using
-- 
-- \[`\]
-- \[\operatorname{Si}(z) = \frac{i}{2} \left[
--     e^{iz} U(1,1,-iz) - e^{-iz} U(1,1,iz) + 
--     \log(-iz) - \log(iz) \right]\]
-- 
-- \[`\]
-- \[\operatorname{Si}(z) = z {}_1F_2(\tfrac{1}{2}; \tfrac{3}{2}, \tfrac{3}{2}; -\tfrac{z^2}{4})\]
-- 
-- and an automatic algorithm choice.
foreign import ccall "acb_hypgeom.h acb_hypgeom_si"
  acb_hypgeom_si :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /_acb_hypgeom_si_series/ /res/ /z/ /zlen/ /len/ /prec/ 
--
foreign import ccall "acb_hypgeom.h _acb_hypgeom_si_series"
  _acb_hypgeom_si_series :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> CLong -> IO ()

-- | /acb_hypgeom_si_series/ /res/ /z/ /len/ /prec/ 
--
-- Computes the sine integral of the power series /z/, truncated to length
-- /len/.
foreign import ccall "acb_hypgeom.h acb_hypgeom_si_series"
  acb_hypgeom_si_series :: Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> CLong -> IO ()

-- | /acb_hypgeom_ci_asymp/ /res/ /z/ /prec/ 
--
foreign import ccall "acb_hypgeom.h acb_hypgeom_ci_asymp"
  acb_hypgeom_ci_asymp :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_hypgeom_ci_2f3/ /res/ /z/ /prec/ 
--
foreign import ccall "acb_hypgeom.h acb_hypgeom_ci_2f3"
  acb_hypgeom_ci_2f3 :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_hypgeom_ci/ /res/ /z/ /prec/ 
--
-- Computes the cosine integral \(\operatorname{Ci}(z)\), respectively
-- using
-- 
-- \[`\]
-- \[\operatorname{Ci}(z) = \log(z) - \frac{1}{2} \left[
--     e^{iz} U(1,1,-iz) + e^{-iz} U(1,1,iz) + 
--     \log(-iz) + \log(iz) \right]\]
-- 
-- \[`\]
-- \[\operatorname{Ci}(z) = -\tfrac{z^2}{4}
--     {}_2F_3(1, 1; 2, 2, \tfrac{3}{2}; -\tfrac{z^2}{4})
--     + \log(z) + \gamma\]
-- 
-- and an automatic algorithm choice.
foreign import ccall "acb_hypgeom.h acb_hypgeom_ci"
  acb_hypgeom_ci :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /_acb_hypgeom_ci_series/ /res/ /z/ /zlen/ /len/ /prec/ 
--
foreign import ccall "acb_hypgeom.h _acb_hypgeom_ci_series"
  _acb_hypgeom_ci_series :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> CLong -> IO ()

-- | /acb_hypgeom_ci_series/ /res/ /z/ /len/ /prec/ 
--
-- Computes the cosine integral of the power series /z/, truncated to
-- length /len/.
foreign import ccall "acb_hypgeom.h acb_hypgeom_ci_series"
  acb_hypgeom_ci_series :: Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> CLong -> IO ()

-- | /acb_hypgeom_shi/ /res/ /z/ /prec/ 
--
-- Computes the hyperbolic sine integral
-- \(\operatorname{Shi}(z) = -i \operatorname{Si}(iz)\). This is a trivial
-- wrapper of @acb_hypgeom_si@.
foreign import ccall "acb_hypgeom.h acb_hypgeom_shi"
  acb_hypgeom_shi :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /_acb_hypgeom_shi_series/ /res/ /z/ /zlen/ /len/ /prec/ 
--
foreign import ccall "acb_hypgeom.h _acb_hypgeom_shi_series"
  _acb_hypgeom_shi_series :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> CLong -> IO ()

-- | /acb_hypgeom_shi_series/ /res/ /z/ /len/ /prec/ 
--
-- Computes the hyperbolic sine integral of the power series /z/, truncated
-- to length /len/.
foreign import ccall "acb_hypgeom.h acb_hypgeom_shi_series"
  acb_hypgeom_shi_series :: Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> CLong -> IO ()

-- | /acb_hypgeom_chi_asymp/ /res/ /z/ /prec/ 
--
foreign import ccall "acb_hypgeom.h acb_hypgeom_chi_asymp"
  acb_hypgeom_chi_asymp :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_hypgeom_chi_2f3/ /res/ /z/ /prec/ 
--
foreign import ccall "acb_hypgeom.h acb_hypgeom_chi_2f3"
  acb_hypgeom_chi_2f3 :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_hypgeom_chi/ /res/ /z/ /prec/ 
--
-- Computes the hyperbolic cosine integral \(\operatorname{Chi}(z)\),
-- respectively using
-- 
-- \[`\]
-- \[\operatorname{Chi}(z) = -\frac{1}{2} \left[
--     e^{z} U(1,1,-z) + e^{-z} U(1,1,z) + 
--     \log(-z) - \log(z) \right]\]
-- 
-- \[`\]
-- \[\operatorname{Chi}(z) = \tfrac{z^2}{4}
--     {}_2F_3(1, 1; 2, 2, \tfrac{3}{2}; \tfrac{z^2}{4})
--     + \log(z) + \gamma\]
-- 
-- and an automatic algorithm choice.
foreign import ccall "acb_hypgeom.h acb_hypgeom_chi"
  acb_hypgeom_chi :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /_acb_hypgeom_chi_series/ /res/ /z/ /zlen/ /len/ /prec/ 
--
foreign import ccall "acb_hypgeom.h _acb_hypgeom_chi_series"
  _acb_hypgeom_chi_series :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> CLong -> IO ()

-- | /acb_hypgeom_chi_series/ /res/ /z/ /len/ /prec/ 
--
-- Computes the hyperbolic cosine integral of the power series /z/,
-- truncated to length /len/.
foreign import ccall "acb_hypgeom.h acb_hypgeom_chi_series"
  acb_hypgeom_chi_series :: Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> CLong -> IO ()

-- | /acb_hypgeom_li/ /res/ /z/ /offset/ /prec/ 
--
-- If /offset/ is zero, computes the logarithmic integral
-- \(\operatorname{li}(z) = \operatorname{Ei}(\log(z))\).
-- 
-- If /offset/ is nonzero, computes the offset logarithmic integral
-- \(\operatorname{Li}(z) = \operatorname{li}(z) - \operatorname{li}(2)\).
foreign import ccall "acb_hypgeom.h acb_hypgeom_li"
  acb_hypgeom_li :: Ptr CAcb -> Ptr CAcb -> CInt -> CLong -> IO ()

-- | /_acb_hypgeom_li_series/ /res/ /z/ /zlen/ /offset/ /len/ /prec/ 
--
foreign import ccall "acb_hypgeom.h _acb_hypgeom_li_series"
  _acb_hypgeom_li_series :: Ptr CAcb -> Ptr CAcb -> CLong -> CInt -> CLong -> CLong -> IO ()

-- | /acb_hypgeom_li_series/ /res/ /z/ /offset/ /len/ /prec/ 
--
-- Computes the logarithmic integral (optionally the offset version) of the
-- power series /z/, truncated to length /len/.
foreign import ccall "acb_hypgeom.h acb_hypgeom_li_series"
  acb_hypgeom_li_series :: Ptr CAcbPoly -> Ptr CAcbPoly -> CInt -> CLong -> CLong -> IO ()

-- Gauss hypergeometric function -----------------------------------------------

-- The following methods compute the Gauss hypergeometric function
--
-- \[`\]
-- \[F(z) = {}_2F_1(a,b,c,z) = \sum_{k=0}^{\infty} \frac{(a)_k (b)_k}{(c)_k} \frac{z^k}{k!}\]
--
-- or the regularized version operatorname{mathbf{F}}(z) =
-- operatorname{mathbf{F}}(a,b,c,z) = {}_2F_1(a,b,c,z) \/ Gamma(c) if the
-- flag /regularized/ is set.
--
-- | /acb_hypgeom_2f1_continuation/ /res0/ /res1/ /a/ /b/ /c/ /z0/ /z1/ /f0/ /f1/ /prec/ 
--
-- Given \(F(z_0), F'(z_0)\) in /f0/, /f1/, sets /res0/ and /res1/ to
-- \(F(z_1), F'(z_1)\) by integrating the hypergeometric differential
-- equation along a straight-line path. The evaluation points should be
-- well-isolated from the singular points 0 and 1.
foreign import ccall "acb_hypgeom.h acb_hypgeom_2f1_continuation"
  acb_hypgeom_2f1_continuation :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_hypgeom_2f1_series_direct/ /res/ /a/ /b/ /c/ /z/ /regularized/ /len/ /prec/ 
--
-- Computes \(F(z)\) of the given power series truncated to length /len/,
-- using direct summation of the hypergeometric series.
foreign import ccall "acb_hypgeom.h acb_hypgeom_2f1_series_direct"
  acb_hypgeom_2f1_series_direct :: Ptr CAcbPoly -> Ptr CAcbPoly -> Ptr CAcbPoly -> Ptr CAcbPoly -> Ptr CAcbPoly -> CInt -> CLong -> CLong -> IO ()

-- | /acb_hypgeom_2f1_direct/ /res/ /a/ /b/ /c/ /z/ /regularized/ /prec/ 
--
-- Computes \(F(z)\) using direct summation of the hypergeometric series.
foreign import ccall "acb_hypgeom.h acb_hypgeom_2f1_direct"
  acb_hypgeom_2f1_direct :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CInt -> CLong -> IO ()

-- | /acb_hypgeom_2f1_transform/ /res/ /a/ /b/ /c/ /z/ /flags/ /which/ /prec/ 
--
foreign import ccall "acb_hypgeom.h acb_hypgeom_2f1_transform"
  acb_hypgeom_2f1_transform :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CInt -> CInt -> CLong -> IO ()

-- | /acb_hypgeom_2f1_transform_limit/ /res/ /a/ /b/ /c/ /z/ /regularized/ /which/ /prec/ 
--
-- Computes \(F(z)\) using an argument transformation determined by the
-- flag /which/. Legal values are 1 for \(z/(z-1)\), 2 for \(1/z\), 3 for
-- \(1/(1-z)\), 4 for \(1-z\), and 5 for \(1-1/z\).
-- 
-- The /transform_limit/ version assumes that /which/ is not 1. If /which/
-- is 2 or 3, it assumes that \(b-a\) represents an exact integer. If
-- /which/ is 4 or 5, it assumes that \(c-a-b\) represents an exact
-- integer. In these cases, it computes the correct limit value.
-- 
-- See @acb_hypgeom_2f1@ for the meaning of /flags/.
foreign import ccall "acb_hypgeom.h acb_hypgeom_2f1_transform_limit"
  acb_hypgeom_2f1_transform_limit :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CInt -> CInt -> CLong -> IO ()

-- | /acb_hypgeom_2f1_corner/ /res/ /a/ /b/ /c/ /z/ /regularized/ /prec/ 
--
-- Computes \(F(z)\) near the corner cases \(\exp(\pm \pi i \sqrt{3})\) by
-- analytic continuation.
foreign import ccall "acb_hypgeom.h acb_hypgeom_2f1_corner"
  acb_hypgeom_2f1_corner :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CInt -> CLong -> IO ()

-- | /acb_hypgeom_2f1_choose/ /z/ 
--
-- Chooses a method to compute the function based on the location of /z/ in
-- the complex plane. If the return value is 0, direct summation should be
-- used. If the return value is 1 to 5, the transformation with this index
-- in @acb_hypgeom_2f1_transform@ should be used. If the return value is 6,
-- the corner case algorithm should be used.
foreign import ccall "acb_hypgeom.h acb_hypgeom_2f1_choose"
  acb_hypgeom_2f1_choose :: Ptr CAcb -> IO CInt

-- | /acb_hypgeom_2f1/ /res/ /a/ /b/ /c/ /z/ /flags/ /prec/ 
--
-- Computes \(F(z)\) or \(\operatorname{\mathbf{F}}(z)\) using an automatic
-- algorithm choice.
-- 
-- The following bit fields can be set in /flags/:
-- 
-- -   /ACB_HYPGEOM_2F1_REGULARIZED/ - computes the regularized
--     hypergeometric function \(\operatorname{\mathbf{F}}(z)\). Setting
--     /flags/ to 1 is the same as just toggling this option.
-- -   /ACB_HYPGEOM_2F1_AB/ - \(a-b\) is an integer.
-- -   /ACB_HYPGEOM_2F1_ABC/ - \(a+b-c\) is an integer.
-- -   /ACB_HYPGEOM_2F1_AC/ - \(a-c\) is an integer.
-- -   /ACB_HYPGEOM_2F1_BC/ - \(b-c\) is an integer.
-- 
-- The last four flags can be set to indicate that the respective parameter
-- differences are known to represent exact integers, even if the input
-- intervals are inexact. This allows the correct limits to be evaluated
-- when applying transformation formulas. For example, to evaluate
-- \({}_2F_1(\sqrt{2}, 1/2, \sqrt{2}+3/2, 9/10)\), the /ABC/ flag should be
-- set. If not set, the result will be an indeterminate interval due to
-- internally dividing by an interval containing zero. If the parameters
-- are exact floating-point numbers (including exact integers or
-- half-integers), then the limits are computed automatically, and setting
-- these flags is unnecessary.
-- 
-- Currently, only the /AB/ and /ABC/ flags are used this way; the /AC/ and
-- /BC/ flags might be used in the future.
foreign import ccall "acb_hypgeom.h acb_hypgeom_2f1"
  acb_hypgeom_2f1 :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CInt -> CLong -> IO ()

-- Orthogonal polynomials and functions ----------------------------------------

-- | /acb_hypgeom_chebyshev_t/ /res/ /n/ /z/ /prec/ 
--
foreign import ccall "acb_hypgeom.h acb_hypgeom_chebyshev_t"
  acb_hypgeom_chebyshev_t :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_hypgeom_chebyshev_u/ /res/ /n/ /z/ /prec/ 
--
-- Computes the Chebyshev polynomial (or Chebyshev function) of first or
-- second kind
-- 
-- \[`\]
-- \[T_n(z) = {}_2F_1\left(-n,n,\frac{1}{2},\frac{1-z}{2}\right)\]
-- 
-- \[`\]
-- \[U_n(z) = (n+1) {}_2F_1\left(-n,n+2,\frac{3}{2},\frac{1-z}{2}\right).\]
-- 
-- The hypergeometric series definitions are only used for computation near
-- the point 1. In general, trigonometric representations are used. For
-- word-size integer /n/, @acb_chebyshev_t_ui@ and @acb_chebyshev_u_ui@ are
-- called.
foreign import ccall "acb_hypgeom.h acb_hypgeom_chebyshev_u"
  acb_hypgeom_chebyshev_u :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_hypgeom_jacobi_p/ /res/ /n/ /a/ /b/ /z/ /prec/ 
--
-- Computes the Jacobi polynomial (or Jacobi function)
-- 
-- \[`\]
-- \[P_n^{(a,b)}(z)=\frac{(a+1)_n}{\Gamma(n+1)} {}_2F_1\left(-n,n+a+b+1,a+1,\frac{1-z}{2}\right).\]
-- 
-- For nonnegative integer /n/, this is a polynomial in /a/, /b/ and /z/,
-- even when the parameters are such that the hypergeometric series is
-- undefined. In such cases, the polynomial is evaluated using direct
-- methods.
foreign import ccall "acb_hypgeom.h acb_hypgeom_jacobi_p"
  acb_hypgeom_jacobi_p :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_hypgeom_gegenbauer_c/ /res/ /n/ /m/ /z/ /prec/ 
--
-- Computes the Gegenbauer polynomial (or Gegenbauer function)
-- 
-- \[`\]
-- \[C_n^{m}(z)=\frac{(2m)_n}{\Gamma(n+1)} {}_2F_1\left(-n,2m+n,m+\frac{1}{2},\frac{1-z}{2}\right).\]
-- 
-- For nonnegative integer /n/, this is a polynomial in /m/ and /z/, even
-- when the parameters are such that the hypergeometric series is
-- undefined. In such cases, the polynomial is evaluated using direct
-- methods.
foreign import ccall "acb_hypgeom.h acb_hypgeom_gegenbauer_c"
  acb_hypgeom_gegenbauer_c :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_hypgeom_laguerre_l/ /res/ /n/ /m/ /z/ /prec/ 
--
-- Computes the Laguerre polynomial (or Laguerre function)
-- 
-- \[`\]
-- \[L_n^{m}(z)=\frac{(m+1)_n}{\Gamma(n+1)} {}_1F_1\left(-n,m+1,z\right).\]
-- 
-- For nonnegative integer /n/, this is a polynomial in /m/ and /z/, even
-- when the parameters are such that the hypergeometric series is
-- undefined. In such cases, the polynomial is evaluated using direct
-- methods.
-- 
-- There are at least two incompatible ways to define the Laguerre function
-- when /n/ is a negative integer. One possibility when \(m = 0\) is to
-- define \(L_{-n}^0(z) = e^z L_{n-1}^0(-z)\). Another possibility is to
-- cover this case with the recurrence relation
-- \(L_{n-1}^m(z) + L_n^{m-1}(z) = L_n^m(z)\). Currently, we leave this
-- case undefined (returning indeterminate).
foreign import ccall "acb_hypgeom.h acb_hypgeom_laguerre_l"
  acb_hypgeom_laguerre_l :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_hypgeom_hermite_h/ /res/ /n/ /z/ /prec/ 
--
-- Computes the Hermite polynomial (or Hermite function)
-- 
-- \[`\]
-- \[H_n(z) = 2^n \sqrt{\pi} \left(
--     \frac{1}{\Gamma((1-n)/2)} {}_1F_1\left(-\frac{n}{2},\frac{1}{2},z^2\right)
--     - 
--     \frac{2z}{\Gamma(-n/2)} {}_1F_1\left(\frac{1-n}{2},\frac{3}{2},z^2\right)\right).\]
foreign import ccall "acb_hypgeom.h acb_hypgeom_hermite_h"
  acb_hypgeom_hermite_h :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_hypgeom_legendre_p/ /res/ /n/ /m/ /z/ /type/ /prec/ 
--
-- Sets /res/ to the associated Legendre function of the first kind
-- evaluated for degree /n/, order /m/, and argument /z/. When /m/ is zero,
-- this reduces to the Legendre polynomial \(P_n(z)\).
-- 
-- Many different branch cut conventions appear in the literature. If
-- /type/ is 0, the version
-- 
-- \[`\]
-- \[P_n^m(z) = \frac{(1+z)^{m/2}}{(1-z)^{m/2}}
--     \mathbf{F}\left(-n, n+1, 1-m, \frac{1-z}{2}\right)\]
-- 
-- is computed, and if /type/ is 1, the alternative version
-- 
-- \[`\]
-- \[{\mathcal P}_n^m(z) = \frac{(z+1)^{m/2}}{(z-1)^{m/2}}
--     \mathbf{F}\left(-n, n+1, 1-m, \frac{1-z}{2}\right).\]
-- 
-- is computed. Type 0 and type 1 respectively correspond to type 2 and
-- type 3 in /Mathematica/ and /mpmath/.
foreign import ccall "acb_hypgeom.h acb_hypgeom_legendre_p"
  acb_hypgeom_legendre_p :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CInt -> CLong -> IO ()

-- | /acb_hypgeom_legendre_q/ /res/ /n/ /m/ /z/ /type/ /prec/ 
--
-- Sets /res/ to the associated Legendre function of the second kind
-- evaluated for degree /n/, order /m/, and argument /z/. When /m/ is zero,
-- this reduces to the Legendre function \(Q_n(z)\).
-- 
-- Many different branch cut conventions appear in the literature. If
-- /type/ is 0, the version
-- 
-- \[`\]
-- \[Q_n^m(z) = \frac{\pi}{2 \sin(\pi m)}
--     \left( \cos(\pi m) P_n^m(z) -
--     \frac{\Gamma(1+m+n)}{\Gamma(1-m+n)} P_n^{-m}(z)\right)\]
-- 
-- is computed, and if /type/ is 1, the alternative version
-- 
-- \[`\]
-- \[\mathcal{Q}_n^m(z) = \frac{\pi}{2 \sin(\pi m)} e^{\pi i m}
--     \left( \mathcal{P}_n^m(z) -
--     \frac{\Gamma(1+m+n)}{\Gamma(1-m+n)} \mathcal{P}_n^{-m}(z)\right)\]
-- 
-- is computed. Type 0 and type 1 respectively correspond to type 2 and
-- type 3 in /Mathematica/ and /mpmath/.
-- 
-- When /m/ is an integer, either expression is interpreted as a limit. We
-- make use of the connection formulas < [WQ3a]>, < [WQ3b]> and < [WQ3c]>
-- to allow computing the function even in the limiting case. (The formula
-- < [WQ3d]> would be useful, but is incorrect in the lower half plane.)
foreign import ccall "acb_hypgeom.h acb_hypgeom_legendre_q"
  acb_hypgeom_legendre_q :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CInt -> CLong -> IO ()

-- | /acb_hypgeom_legendre_p_uiui_rec/ /res/ /n/ /m/ /z/ /prec/ 
--
-- For nonnegative integer /n/ and /m/, uses recurrence relations to
-- evaluate \((1-z^2)^{-m/2} P_n^m(z)\) which is a polynomial in /z/.
foreign import ccall "acb_hypgeom.h acb_hypgeom_legendre_p_uiui_rec"
  acb_hypgeom_legendre_p_uiui_rec :: Ptr CAcb -> CULong -> CULong -> Ptr CAcb -> CLong -> IO ()

-- | /acb_hypgeom_spherical_y/ /res/ /n/ /m/ /theta/ /phi/ /prec/ 
--
-- Computes the spherical harmonic of degree /n/, order /m/, latitude angle
-- /theta/, and longitude angle /phi/, normalized such that
-- 
-- \[`\]
-- \[Y_n^m(\theta, \phi) = \sqrt{\frac{2n+1}{4\pi} \frac{(n-m)!}{(n+m)!}} e^{im\phi} P_n^m(\cos(\theta)).\]
-- 
-- The definition is extended to negative /m/ and /n/ by symmetry. This
-- function is a polynomial in \(\cos(\theta)\) and \(\sin(\theta)\). We
-- evaluate it using @acb_hypgeom_legendre_p_uiui_rec@.
foreign import ccall "acb_hypgeom.h acb_hypgeom_spherical_y"
  acb_hypgeom_spherical_y :: Ptr CAcb -> CLong -> CLong -> Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- Dilogarithm -----------------------------------------------------------------

-- The dilogarithm function is given by
-- \(\operatorname{Li}_2(z) = -\int_0^z \frac{\log(1-t)}{t} dt = z {}_3F_2(1,1,1,2,2,z)\).
--



-- | /acb_hypgeom_dilog_zero_taylor/ /res/ /z/ /prec/ 
--
-- Computes the dilogarithm for /z/ close to 0 using the hypergeometric
-- series (effective only when \(|z| \ll 1\)).
foreign import ccall "acb_hypgeom.h acb_hypgeom_dilog_zero_taylor"
  acb_hypgeom_dilog_zero_taylor :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_hypgeom_dilog_zero/ /res/ /z/ /prec/ 
--
-- Computes the dilogarithm for /z/ close to 0, using the bit-burst
-- algorithm instead of the hypergeometric series directly at very high
-- precision.
foreign import ccall "acb_hypgeom.h acb_hypgeom_dilog_zero"
  acb_hypgeom_dilog_zero :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_hypgeom_dilog_transform/ /res/ /z/ /algorithm/ /prec/ 
--
-- Computes the dilogarithm by applying one of the transformations \(1/z\),
-- \(1-z\), \(z/(z-1)\), \(1/(1-z)\), indexed by /algorithm/ from 1 to 4,
-- and calling @acb_hypgeom_dilog_zero@ with the reduced variable.
-- Alternatively, for /algorithm/ between 5 and 7, starts from the
-- respective point \(\pm i\), \((1\pm i)/2\), \((1\pm i)/2\) (with the
-- sign chosen according to the midpoint of /z/) and computes the
-- dilogarithm by the bit-burst method.
foreign import ccall "acb_hypgeom.h acb_hypgeom_dilog_transform"
  acb_hypgeom_dilog_transform :: Ptr CAcb -> Ptr CAcb -> CInt -> CLong -> IO ()

-- | /acb_hypgeom_dilog_continuation/ /res/ /a/ /z/ /prec/ 
--
-- Computes \(\operatorname{Li}_2(z) - \operatorname{Li}_2(a)\) using
-- Taylor expansion at /a/. Binary splitting is used. Both /a/ and /z/
-- should be well isolated from the points 0 and 1, except that /a/ may be
-- exactly 0. If the straight line path from /a/ to /b/ crosses the branch
-- cut, this method provides continuous analytic continuation instead of
-- computing the principal branch.
foreign import ccall "acb_hypgeom.h acb_hypgeom_dilog_continuation"
  acb_hypgeom_dilog_continuation :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_hypgeom_dilog_bitburst/ /res/ /z0/ /z/ /prec/ 
--
-- Sets /z0/ to a point with short bit expansion close to /z/ and sets
-- /res/ to \(\operatorname{Li}_2(z) - \operatorname{Li}_2(z_0)\), computed
-- using the bit-burst algorithm.
foreign import ccall "acb_hypgeom.h acb_hypgeom_dilog_bitburst"
  acb_hypgeom_dilog_bitburst :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_hypgeom_dilog/ /res/ /z/ /prec/ 
--
-- Computes the dilogarithm using a default algorithm choice.
foreign import ccall "acb_hypgeom.h acb_hypgeom_dilog"
  acb_hypgeom_dilog :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

