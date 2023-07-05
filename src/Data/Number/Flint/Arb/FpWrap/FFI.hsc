{-# language
    CApiFFI
  , FlexibleInstances
  , ForeignFunctionInterface
  , MultiParamTypeClasses
  , TupleSections
  , TypeFamilies
  #-}

module Data.Number.Flint.Arb.FpWrap.FFI (
  -- * Floating-point wrappers of Arb mathematical functions
  -- * Option and return flags
    FpWrapReturn (..)
  , fpwrap_success
  , fpwrap_unable
  , fpwrap_accurate_parts
  , fpwrap_correct_rounding
  , fpwrap_work_limit
  -- * Elementary functions
  , arb_fpwrap_double_exp
  , arb_fpwrap_cdouble_exp
  , arb_fpwrap_double_expm1
  , arb_fpwrap_cdouble_expm1
  , arb_fpwrap_double_log
  , arb_fpwrap_cdouble_log
  , arb_fpwrap_double_log1p
  , arb_fpwrap_cdouble_log1p
  , arb_fpwrap_double_pow
  , arb_fpwrap_cdouble_pow
  , arb_fpwrap_double_sqrt
  , arb_fpwrap_cdouble_sqrt
  , arb_fpwrap_double_rsqrt
  , arb_fpwrap_cdouble_rsqrt
  , arb_fpwrap_double_cbrt
  , arb_fpwrap_cdouble_cbrt
  , arb_fpwrap_double_sin
  , arb_fpwrap_cdouble_sin
  , arb_fpwrap_double_cos
  , arb_fpwrap_cdouble_cos
  , arb_fpwrap_double_tan
  , arb_fpwrap_cdouble_tan
  , arb_fpwrap_double_cot
  , arb_fpwrap_cdouble_cot
  , arb_fpwrap_double_sec
  , arb_fpwrap_cdouble_sec
  , arb_fpwrap_double_csc
  , arb_fpwrap_cdouble_csc
  , arb_fpwrap_double_sinc
  , arb_fpwrap_cdouble_sinc
  , arb_fpwrap_double_sin_pi
  , arb_fpwrap_cdouble_sin_pi
  , arb_fpwrap_double_cos_pi
  , arb_fpwrap_cdouble_cos_pi
  , arb_fpwrap_double_tan_pi
  , arb_fpwrap_cdouble_tan_pi
  , arb_fpwrap_double_cot_pi
  , arb_fpwrap_cdouble_cot_pi
  , arb_fpwrap_double_sinc_pi
  , arb_fpwrap_cdouble_sinc_pi
  , arb_fpwrap_double_asin
  , arb_fpwrap_cdouble_asin
  , arb_fpwrap_double_acos
  , arb_fpwrap_cdouble_acos
  , arb_fpwrap_double_atan
  , arb_fpwrap_cdouble_atan
  , arb_fpwrap_double_atan2
  , arb_fpwrap_double_asinh
  , arb_fpwrap_cdouble_asinh
  , arb_fpwrap_double_acosh
  , arb_fpwrap_cdouble_acosh
  , arb_fpwrap_double_atanh
  , arb_fpwrap_cdouble_atanh
  , arb_fpwrap_double_lambertw
  , arb_fpwrap_cdouble_lambertw
  -- * Gamma, zeta and related functions
  , arb_fpwrap_double_rising
  , arb_fpwrap_cdouble_rising
  , arb_fpwrap_double_gamma
  , arb_fpwrap_cdouble_gamma
  , arb_fpwrap_double_rgamma
  , arb_fpwrap_cdouble_rgamma
  , arb_fpwrap_double_lgamma
  , arb_fpwrap_cdouble_lgamma
  , arb_fpwrap_double_digamma
  , arb_fpwrap_cdouble_digamma
  , arb_fpwrap_double_zeta
  , arb_fpwrap_cdouble_zeta
  , arb_fpwrap_double_hurwitz_zeta
  , arb_fpwrap_cdouble_hurwitz_zeta
  , arb_fpwrap_double_lerch_phi
  , arb_fpwrap_cdouble_lerch_phi
  , arb_fpwrap_double_barnes_g
  , arb_fpwrap_cdouble_barnes_g
  , arb_fpwrap_double_log_barnes_g
  , arb_fpwrap_cdouble_log_barnes_g
  , arb_fpwrap_double_polygamma
  , arb_fpwrap_cdouble_polygamma
  , arb_fpwrap_double_polylog
  , arb_fpwrap_cdouble_polylog
  , arb_fpwrap_cdouble_dirichlet_eta
  , arb_fpwrap_cdouble_riemann_xi
  , arb_fpwrap_cdouble_hardy_theta
  , arb_fpwrap_cdouble_hardy_z
  , arb_fpwrap_cdouble_zeta_zero
  -- * Error functions and exponential integrals
  , arb_fpwrap_double_erf
  , arb_fpwrap_cdouble_erf
  , arb_fpwrap_double_erfc
  , arb_fpwrap_cdouble_erfc
  , arb_fpwrap_double_erfi
  , arb_fpwrap_cdouble_erfi
  , arb_fpwrap_double_erfinv
  , arb_fpwrap_double_erfcinv
  , arb_fpwrap_double_fresnel_s
  , arb_fpwrap_cdouble_fresnel_s
  , arb_fpwrap_double_fresnel_c
  , arb_fpwrap_cdouble_fresnel_c
  , arb_fpwrap_double_gamma_upper
  , arb_fpwrap_cdouble_gamma_upper
  , arb_fpwrap_double_gamma_lower
  , arb_fpwrap_cdouble_gamma_lower
  , arb_fpwrap_double_beta_lower
  , arb_fpwrap_cdouble_beta_lower
  , arb_fpwrap_double_exp_integral_e
  , arb_fpwrap_cdouble_exp_integral_e
  , arb_fpwrap_double_exp_integral_ei
  , arb_fpwrap_cdouble_exp_integral_ei
  , arb_fpwrap_double_sin_integral
  , arb_fpwrap_cdouble_sin_integral
  , arb_fpwrap_double_cos_integral
  , arb_fpwrap_cdouble_cos_integral
  , arb_fpwrap_double_sinh_integral
  , arb_fpwrap_cdouble_sinh_integral
  , arb_fpwrap_double_cosh_integral
  , arb_fpwrap_cdouble_cosh_integral
  , arb_fpwrap_double_log_integral
  , arb_fpwrap_cdouble_log_integral
  , arb_fpwrap_double_dilog
  , arb_fpwrap_cdouble_dilog
  -- * Bessel, Airy and Coulomb functions
  , arb_fpwrap_double_bessel_j
  , arb_fpwrap_cdouble_bessel_j
  , arb_fpwrap_double_bessel_y
  , arb_fpwrap_cdouble_bessel_y
  , arb_fpwrap_double_bessel_i
  , arb_fpwrap_cdouble_bessel_i
  , arb_fpwrap_double_bessel_k
  , arb_fpwrap_cdouble_bessel_k
  , arb_fpwrap_double_bessel_k_scaled
  , arb_fpwrap_cdouble_bessel_k_scaled
  , arb_fpwrap_double_airy_ai
  , arb_fpwrap_cdouble_airy_ai
  , arb_fpwrap_double_airy_ai_prime
  , arb_fpwrap_cdouble_airy_ai_prime
  , arb_fpwrap_double_airy_bi
  , arb_fpwrap_cdouble_airy_bi
  , arb_fpwrap_double_airy_bi_prime
  , arb_fpwrap_cdouble_airy_bi_prime
  , arb_fpwrap_double_airy_ai_zero
  , arb_fpwrap_double_airy_ai_prime_zero
  , arb_fpwrap_double_airy_bi_zero
  , arb_fpwrap_double_airy_bi_prime_zero
  , arb_fpwrap_double_coulomb_f
  , arb_fpwrap_cdouble_coulomb_f
  , arb_fpwrap_double_coulomb_g
  , arb_fpwrap_cdouble_coulomb_g
  , arb_fpwrap_cdouble_coulomb_hpos
  , arb_fpwrap_cdouble_coulomb_hneg
  -- * Orthogonal polynomials
  , arb_fpwrap_double_chebyshev_t
  , arb_fpwrap_cdouble_chebyshev_t
  , arb_fpwrap_double_chebyshev_u
  , arb_fpwrap_cdouble_chebyshev_u
  , arb_fpwrap_double_jacobi_p
  , arb_fpwrap_cdouble_jacobi_p
  , arb_fpwrap_double_gegenbauer_c
  , arb_fpwrap_cdouble_gegenbauer_c
  , arb_fpwrap_double_laguerre_l
  , arb_fpwrap_cdouble_laguerre_l
  , arb_fpwrap_double_hermite_h
  , arb_fpwrap_cdouble_hermite_h
  , arb_fpwrap_double_legendre_p
  , arb_fpwrap_cdouble_legendre_p
  , arb_fpwrap_double_legendre_q
  , arb_fpwrap_cdouble_legendre_q
  , arb_fpwrap_double_legendre_root
  , arb_fpwrap_cdouble_spherical_y
  -- * Hypergeometric functions
  , arb_fpwrap_double_hypgeom_0f1
  , arb_fpwrap_cdouble_hypgeom_0f1
  , arb_fpwrap_double_hypgeom_1f1
  , arb_fpwrap_cdouble_hypgeom_1f1
  , arb_fpwrap_double_hypgeom_u
  , arb_fpwrap_cdouble_hypgeom_u
  , arb_fpwrap_double_hypgeom_2f1
  , arb_fpwrap_cdouble_hypgeom_2f1
  , arb_fpwrap_double_hypgeom_pfq
  , arb_fpwrap_cdouble_hypgeom_pfq
  -- * Elliptic integrals, elliptic functions and modular forms
  , arb_fpwrap_double_agm
  , arb_fpwrap_cdouble_agm
  , arb_fpwrap_cdouble_elliptic_k
  , arb_fpwrap_cdouble_elliptic_e
  , arb_fpwrap_cdouble_elliptic_pi
  , arb_fpwrap_cdouble_elliptic_f
  , arb_fpwrap_cdouble_elliptic_e_inc
  , arb_fpwrap_cdouble_elliptic_pi_inc
  , arb_fpwrap_cdouble_elliptic_rf
  , arb_fpwrap_cdouble_elliptic_rg
  , arb_fpwrap_cdouble_elliptic_rj
  , arb_fpwrap_cdouble_elliptic_p
  , arb_fpwrap_cdouble_elliptic_p_prime
  , arb_fpwrap_cdouble_elliptic_inv_p
  , arb_fpwrap_cdouble_elliptic_zeta
  , arb_fpwrap_cdouble_elliptic_sigma
  , arb_fpwrap_cdouble_jacobi_theta_1
  , arb_fpwrap_cdouble_jacobi_theta_2
  , arb_fpwrap_cdouble_jacobi_theta_3
  , arb_fpwrap_cdouble_jacobi_theta_4
  , arb_fpwrap_cdouble_dedekind_eta
  , arb_fpwrap_cdouble_modular_j
  , arb_fpwrap_cdouble_modular_lambda
  , arb_fpwrap_cdouble_modular_delta
) where 

-- Floating-point wrappers of Arb mathematical functions -----------------------

import Foreign.Ptr
import Foreign.C.Types
import Foreign.Storable

import Data.Complex

#include <flint/arb_fpwrap.h>

--------------------------------------------------------------------------------

-- | Return type for fpwrap functions
newtype FpWrapReturn = FpWrapReturn { _FpWrapReturn :: CInt }
  deriving (Show, Eq)

-- | Indicates an accurate result. (Up to inevitable underflow or
-- overflow in the final conversion to a floating-point result; see
-- above.)
-- 
-- This flag has the numerical value 0.
fpwrap_success = FpWrapReturn #const FPWRAP_SUCCESS
-- | Indicates failure (unable to achieve to target accuracy, possibly
-- because of a singularity). The output is set to NaN.
--
-- This flag has the numerical value 1.
-- Functions take a flags parameter specifying optional rounding and termination behavior. This can be set to 0 to use defaults.
fpwrap_unable = FpWrapReturn #const FPWRAP_UNABLE
-- | For complex output, compute both real and imaginary parts to full
-- relative accuracy. By default (if this flag is not set), complex
-- results are computed to at least 53-bit accuracy as a whole, but if
-- either the real or imaginary part is much smaller than the other,
-- that part can have a large relative error. Setting this flag can
-- result in slower evaluation or failure to converge in some cases.
--
-- This flag has the numerical value 1.
fpwrap_accurate_parts = FpWrapReturn #const FPWRAP_ACCURATE_PARTS
-- | Guarantees correct rounding. By default (if this flag is not
-- set), real results are accurate up to the rounding of the last bit,
-- but the last bit is not guaranteed to be rounded optimally. Setting
-- this flag can result in slower evaluation or failure to converge in
-- some cases. Correct rounding automatically applies to both real and
-- imaginary parts of complex numbers, so it is unnecessary to set
-- both this flag and FPWRAP_ACCURATE_PARTS.
--
-- This flag has the numerical value 2.
fpwrap_correct_rounding = FpWrapReturn #const FPWRAP_CORRECT_ROUNDING
-- | Multiplied by an integer, specifies the maximum working precision
-- to use before giving up. With n * FPWRAP_WORK_LIMIT added to flags,
-- levels of precision will be used. The default is equivalent to ,
-- which for double means trying with a working precision of 64, 128,
-- 256, 512, 1024, 2048, 4096, 8192 bits. With flags = 2 *
-- FPWRAP_WORK_LIMIT, we only try 64 and 128 bits, and with flags = 16
-- * FPWRAP_WORK_LIMIT we go up to 2097152 bits.
--
-- This flag has the numerical value 65536.
fpwrap_work_limit = FpWrapReturn #const FPWRAP_WORK_LIMIT

-- Functions -------------------------------------------------------------------

-- Elementary functions --------------------------------------------------------

-- | /arb_fpwrap_double_exp/ /res/ /x/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_exp_"
  arb_fpwrap_double_exp :: Ptr CDouble -> CDouble -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_exp/ /res/ /x/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_exp_"
  arb_fpwrap_cdouble_exp :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_expm1/ /res/ /x/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_expm1_"
  arb_fpwrap_double_expm1 :: Ptr CDouble -> CDouble -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_expm1/ /res/ /x/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_expm1_"
  arb_fpwrap_cdouble_expm1 :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_log/ /res/ /x/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_log_"
  arb_fpwrap_double_log :: Ptr CDouble -> CDouble -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_log/ /res/ /x/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_log_"
  arb_fpwrap_cdouble_log :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_log1p/ /res/ /x/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_log1p_"
  arb_fpwrap_double_log1p :: Ptr CDouble -> CDouble -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_log1p/ /res/ /x/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_log1p_"
  arb_fpwrap_cdouble_log1p :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_pow/ /res/ /x/ /y/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_pow_"
  arb_fpwrap_double_pow :: Ptr CDouble -> CDouble -> CDouble -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_pow/ /res/ /x/ /y/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_pow_"
  arb_fpwrap_cdouble_pow :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_sqrt/ /res/ /x/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_sqrt_"
  arb_fpwrap_double_sqrt :: Ptr CDouble -> CDouble -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_sqrt/ /res/ /x/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_sqrt_"
  arb_fpwrap_cdouble_sqrt :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_rsqrt/ /res/ /x/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_rsqrt_"
  arb_fpwrap_double_rsqrt :: Ptr CDouble -> CDouble -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_rsqrt/ /res/ /x/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_rsqrt_"
  arb_fpwrap_cdouble_rsqrt :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_cbrt/ /res/ /x/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_cbrt_"
  arb_fpwrap_double_cbrt :: Ptr CDouble -> CDouble -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_cbrt/ /res/ /x/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_cbrt_"
  arb_fpwrap_cdouble_cbrt :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_sin/ /res/ /x/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_sin_"
  arb_fpwrap_double_sin :: Ptr CDouble -> CDouble -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_sin/ /res/ /x/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_sin_"
  arb_fpwrap_cdouble_sin :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_cos/ /res/ /x/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_cos_"
  arb_fpwrap_double_cos :: Ptr CDouble -> CDouble -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_cos/ /res/ /x/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_cos_"
  arb_fpwrap_cdouble_cos :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_tan/ /res/ /x/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_tan_"
  arb_fpwrap_double_tan :: Ptr CDouble -> CDouble -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_tan/ /res/ /x/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_tan_"
  arb_fpwrap_cdouble_tan :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_cot/ /res/ /x/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_cot_"
  arb_fpwrap_double_cot :: Ptr CDouble -> CDouble -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_cot/ /res/ /x/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_cot_"
  arb_fpwrap_cdouble_cot :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_sec/ /res/ /x/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_sec_"
  arb_fpwrap_double_sec :: Ptr CDouble -> CDouble -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_sec/ /res/ /x/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_sec_"
  arb_fpwrap_cdouble_sec :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_csc/ /res/ /x/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_csc_"
  arb_fpwrap_double_csc :: Ptr CDouble -> CDouble -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_csc/ /res/ /x/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_csc_"
  arb_fpwrap_cdouble_csc :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_sinc/ /res/ /x/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_sinc_"
  arb_fpwrap_double_sinc :: Ptr CDouble -> CDouble -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_sinc/ /res/ /x/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_sinc_"
  arb_fpwrap_cdouble_sinc :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_sin_pi/ /res/ /x/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_sin_pi_"
  arb_fpwrap_double_sin_pi :: Ptr CDouble -> CDouble -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_sin_pi/ /res/ /x/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_sin_pi_"
  arb_fpwrap_cdouble_sin_pi :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_cos_pi/ /res/ /x/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_cos_pi_"
  arb_fpwrap_double_cos_pi :: Ptr CDouble -> CDouble -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_cos_pi/ /res/ /x/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_cos_pi_"
  arb_fpwrap_cdouble_cos_pi :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_tan_pi/ /res/ /x/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_tan_pi_"
  arb_fpwrap_double_tan_pi :: Ptr CDouble -> CDouble -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_tan_pi/ /res/ /x/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_tan_pi_"
  arb_fpwrap_cdouble_tan_pi :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_cot_pi/ /res/ /x/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_cot_pi_"
  arb_fpwrap_double_cot_pi :: Ptr CDouble -> CDouble -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_cot_pi/ /res/ /x/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_cot_pi_"
  arb_fpwrap_cdouble_cot_pi :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_sinc_pi/ /res/ /x/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_sinc_pi_"
  arb_fpwrap_double_sinc_pi :: Ptr CDouble -> CDouble -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_sinc_pi/ /res/ /x/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_sinc_pi_"
  arb_fpwrap_cdouble_sinc_pi :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_asin/ /res/ /x/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_asin_"
  arb_fpwrap_double_asin :: Ptr CDouble -> CDouble -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_asin/ /res/ /x/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_asin_"
  arb_fpwrap_cdouble_asin :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_acos/ /res/ /x/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_acos_"
  arb_fpwrap_double_acos :: Ptr CDouble -> CDouble -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_acos/ /res/ /x/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_acos_"
  arb_fpwrap_cdouble_acos :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_atan/ /res/ /x/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_atan_"
  arb_fpwrap_double_atan :: Ptr CDouble -> CDouble -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_atan/ /res/ /x/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_atan_"
  arb_fpwrap_cdouble_atan :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_atan2/ /res/ /x1/ /x2/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_atan2_"
  arb_fpwrap_double_atan2 :: Ptr CDouble -> CDouble -> CDouble -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_asinh/ /res/ /x/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_asinh_"
  arb_fpwrap_double_asinh :: Ptr CDouble -> CDouble -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_asinh/ /res/ /x/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_asinh_"
  arb_fpwrap_cdouble_asinh :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_acosh/ /res/ /x/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_acosh_"
  arb_fpwrap_double_acosh :: Ptr CDouble -> CDouble -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_acosh/ /res/ /x/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_acosh_"
  arb_fpwrap_cdouble_acosh :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_atanh/ /res/ /x/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_atanh_"
  arb_fpwrap_double_atanh :: Ptr CDouble -> CDouble -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_atanh/ /res/ /x/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_atanh_"
  arb_fpwrap_cdouble_atanh :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_lambertw/ /res/ /x/ /branch/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_lambertw_"
  arb_fpwrap_double_lambertw :: Ptr CDouble -> CDouble -> CLong -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_lambertw/ /res/ /x/ /branch/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_lambertw_"
  arb_fpwrap_cdouble_lambertw :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CLong -> CInt -> IO FpWrapReturn

-- Gamma, zeta and related functions -------------------------------------------

-- | /arb_fpwrap_double_rising/ /res/ /x/ /n/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_rising_"
  arb_fpwrap_double_rising :: Ptr CDouble -> CDouble -> CDouble -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_rising/ /res/ /x/ /n/ /flags/ 
--
-- Rising factorial.
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_rising_"
  arb_fpwrap_cdouble_rising :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_gamma/ /res/ /x/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_gamma_"
  arb_fpwrap_double_gamma :: Ptr CDouble -> CDouble -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_gamma/ /res/ /x/ /flags/ 
--
-- Gamma function.
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_gamma_"
  arb_fpwrap_cdouble_gamma :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_rgamma/ /res/ /x/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_rgamma_"
  arb_fpwrap_double_rgamma :: Ptr CDouble -> CDouble -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_rgamma/ /res/ /x/ /flags/ 
--
-- Reciprocal gamma function.
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_rgamma_"
  arb_fpwrap_cdouble_rgamma :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_lgamma/ /res/ /x/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_lgamma_"
  arb_fpwrap_double_lgamma :: Ptr CDouble -> CDouble -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_lgamma/ /res/ /x/ /flags/ 
--
-- Log-gamma function.
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_lgamma_"
  arb_fpwrap_cdouble_lgamma :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_digamma/ /res/ /x/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_digamma_"
  arb_fpwrap_double_digamma :: Ptr CDouble -> CDouble -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_digamma/ /res/ /x/ /flags/ 
--
-- Digamma function.
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_digamma_"
  arb_fpwrap_cdouble_digamma :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_zeta/ /res/ /x/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_zeta_"
  arb_fpwrap_double_zeta :: Ptr CDouble -> CDouble -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_zeta/ /res/ /x/ /flags/ 
--
-- Riemann zeta function.
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_zeta_"
  arb_fpwrap_cdouble_zeta :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_hurwitz_zeta/ /res/ /s/ /z/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_hurwitz_zeta_"
  arb_fpwrap_double_hurwitz_zeta :: Ptr CDouble -> CDouble -> CDouble -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_hurwitz_zeta/ /res/ /s/ /z/ /flags/ 
--
-- Hurwitz zeta function.
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_hurwitz_zeta_"
  arb_fpwrap_cdouble_hurwitz_zeta :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_lerch_phi/ /res/ /z/ /s/ /a/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_lerch_phi_"
  arb_fpwrap_double_lerch_phi :: Ptr CDouble -> CDouble -> CDouble -> CDouble -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_lerch_phi/ /res/ /z/ /s/ /a/ /flags/ 
--
-- Lerch transcendent.
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_lerch_phi_"
  arb_fpwrap_cdouble_lerch_phi :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_barnes_g/ /res/ /x/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_barnes_g_"
  arb_fpwrap_double_barnes_g :: Ptr CDouble -> CDouble -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_barnes_g/ /res/ /x/ /flags/ 
--
-- Barnes G-function.
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_barnes_g_"
  arb_fpwrap_cdouble_barnes_g :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_log_barnes_g/ /res/ /x/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_log_barnes_g_"
  arb_fpwrap_double_log_barnes_g :: Ptr CDouble -> CDouble -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_log_barnes_g/ /res/ /x/ /flags/ 
--
-- Logarithmic Barnes G-function.
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_log_barnes_g_"
  arb_fpwrap_cdouble_log_barnes_g :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_polygamma/ /res/ /s/ /z/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_polygamma_"
  arb_fpwrap_double_polygamma :: Ptr CDouble -> CDouble -> CDouble -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_polygamma/ /res/ /s/ /z/ /flags/ 
--
-- Polygamma function.
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_polygamma_"
  arb_fpwrap_cdouble_polygamma :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_polylog/ /res/ /s/ /z/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_polylog_"
  arb_fpwrap_double_polylog :: Ptr CDouble -> CDouble -> CDouble -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_polylog/ /res/ /s/ /z/ /flags/ 
--
-- Polylogarithm.
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_polylog_"
  arb_fpwrap_cdouble_polylog :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_cdouble_dirichlet_eta/ /res/ /s/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_dirichlet_eta_"
  arb_fpwrap_cdouble_dirichlet_eta :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_cdouble_riemann_xi/ /res/ /s/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_riemann_xi_"
  arb_fpwrap_cdouble_riemann_xi :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_cdouble_hardy_theta/ /res/ /z/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_hardy_theta_"
  arb_fpwrap_cdouble_hardy_theta :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_cdouble_hardy_z/ /res/ /z/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_hardy_z_"
  arb_fpwrap_cdouble_hardy_z :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_cdouble_zeta_zero/ /res/ /n/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_zeta_zero_"
  arb_fpwrap_cdouble_zeta_zero :: Ptr (Complex CDouble) -> CULong -> CInt -> IO FpWrapReturn

-- Error functions and exponential integrals -----------------------------------

-- | /arb_fpwrap_double_erf/ /res/ /x/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_erf_"
  arb_fpwrap_double_erf :: Ptr CDouble -> CDouble -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_erf/ /res/ /x/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_erf_"
  arb_fpwrap_cdouble_erf :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_erfc/ /res/ /x/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_erfc_"
  arb_fpwrap_double_erfc :: Ptr CDouble -> CDouble -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_erfc/ /res/ /x/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_erfc_"
  arb_fpwrap_cdouble_erfc :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_erfi/ /res/ /x/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_erfi_"
  arb_fpwrap_double_erfi :: Ptr CDouble -> CDouble -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_erfi/ /res/ /x/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_erfi_"
  arb_fpwrap_cdouble_erfi :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_erfinv/ /res/ /x/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_erfinv_"
  arb_fpwrap_double_erfinv :: Ptr CDouble -> CDouble -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_erfcinv/ /res/ /x/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_erfcinv_"
  arb_fpwrap_double_erfcinv :: Ptr CDouble -> CDouble -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_fresnel_s/ /res/ /x/ /normalized/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_fresnel_s_"
  arb_fpwrap_double_fresnel_s :: Ptr CDouble -> CDouble -> CInt -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_fresnel_s/ /res/ /x/ /normalized/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_fresnel_s_"
  arb_fpwrap_cdouble_fresnel_s :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_fresnel_c/ /res/ /x/ /normalized/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_fresnel_c_"
  arb_fpwrap_double_fresnel_c :: Ptr CDouble -> CDouble -> CInt -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_fresnel_c/ /res/ /x/ /normalized/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_fresnel_c_"
  arb_fpwrap_cdouble_fresnel_c :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_gamma_upper/ /res/ /s/ /z/ /regularized/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_gamma_upper_"
  arb_fpwrap_double_gamma_upper :: Ptr CDouble -> CDouble -> CDouble -> CInt -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_gamma_upper/ /res/ /s/ /z/ /regularized/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_gamma_upper_"
  arb_fpwrap_cdouble_gamma_upper :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_gamma_lower/ /res/ /s/ /z/ /regularized/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_gamma_lower_"
  arb_fpwrap_double_gamma_lower :: Ptr CDouble -> CDouble -> CDouble -> CInt -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_gamma_lower/ /res/ /s/ /z/ /regularized/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_gamma_lower_"
  arb_fpwrap_cdouble_gamma_lower :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_beta_lower/ /res/ /a/ /b/ /z/ /regularized/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_beta_lower_"
  arb_fpwrap_double_beta_lower :: Ptr CDouble -> CDouble -> CDouble -> CDouble -> CInt -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_beta_lower/ /res/ /a/ /b/ /z/ /regularized/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_beta_lower_"
  arb_fpwrap_cdouble_beta_lower :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_exp_integral_e/ /res/ /s/ /z/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_exp_integral_e_"
  arb_fpwrap_double_exp_integral_e :: Ptr CDouble -> CDouble -> CDouble -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_exp_integral_e/ /res/ /s/ /z/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_exp_integral_e_"
  arb_fpwrap_cdouble_exp_integral_e :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_exp_integral_ei/ /res/ /x/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_exp_integral_ei_"
  arb_fpwrap_double_exp_integral_ei :: Ptr CDouble -> CDouble -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_exp_integral_ei/ /res/ /x/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_exp_integral_ei_"
  arb_fpwrap_cdouble_exp_integral_ei :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_sin_integral/ /res/ /x/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_sin_integral_"
  arb_fpwrap_double_sin_integral :: Ptr CDouble -> CDouble -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_sin_integral/ /res/ /x/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_sin_integral_"
  arb_fpwrap_cdouble_sin_integral :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_cos_integral/ /res/ /x/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_cos_integral_"
  arb_fpwrap_double_cos_integral :: Ptr CDouble -> CDouble -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_cos_integral/ /res/ /x/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_cos_integral_"
  arb_fpwrap_cdouble_cos_integral :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_sinh_integral/ /res/ /x/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_sinh_integral_"
  arb_fpwrap_double_sinh_integral :: Ptr CDouble -> CDouble -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_sinh_integral/ /res/ /x/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_sinh_integral_"
  arb_fpwrap_cdouble_sinh_integral :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_cosh_integral/ /res/ /x/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_cosh_integral_"
  arb_fpwrap_double_cosh_integral :: Ptr CDouble -> CDouble -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_cosh_integral/ /res/ /x/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_cosh_integral_"
  arb_fpwrap_cdouble_cosh_integral :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_log_integral/ /res/ /x/ /offset/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_log_integral_"
  arb_fpwrap_double_log_integral :: Ptr CDouble -> CDouble -> CInt -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_log_integral/ /res/ /x/ /offset/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_log_integral_"
  arb_fpwrap_cdouble_log_integral :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_dilog/ /res/ /x/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_dilog_"
  arb_fpwrap_double_dilog :: Ptr CDouble -> CDouble -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_dilog/ /res/ /x/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_dilog_"
  arb_fpwrap_cdouble_dilog :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- Bessel, Airy and Coulomb functions ------------------------------------------

-- | /arb_fpwrap_double_bessel_j/ /res/ /nu/ /x/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_bessel_j_"
  arb_fpwrap_double_bessel_j :: Ptr CDouble -> CDouble -> CDouble -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_bessel_j/ /res/ /nu/ /x/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_bessel_j_"
  arb_fpwrap_cdouble_bessel_j :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_bessel_y/ /res/ /nu/ /x/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_bessel_y_"
  arb_fpwrap_double_bessel_y :: Ptr CDouble -> CDouble -> CDouble -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_bessel_y/ /res/ /nu/ /x/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_bessel_y_"
  arb_fpwrap_cdouble_bessel_y :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_bessel_i/ /res/ /nu/ /x/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_bessel_i_"
  arb_fpwrap_double_bessel_i :: Ptr CDouble -> CDouble -> CDouble -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_bessel_i/ /res/ /nu/ /x/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_bessel_i_"
  arb_fpwrap_cdouble_bessel_i :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_bessel_k/ /res/ /nu/ /x/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_bessel_k_"
  arb_fpwrap_double_bessel_k :: Ptr CDouble -> CDouble -> CDouble -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_bessel_k/ /res/ /nu/ /x/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_bessel_k_"
  arb_fpwrap_cdouble_bessel_k :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_bessel_k_scaled/ /res/ /nu/ /x/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_bessel_k_scaled_"
  arb_fpwrap_double_bessel_k_scaled :: Ptr CDouble -> CDouble -> CDouble -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_bessel_k_scaled/ /res/ /nu/ /x/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_bessel_k_scaled_"
  arb_fpwrap_cdouble_bessel_k_scaled :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_airy_ai/ /res/ /x/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_airy_ai_"
  arb_fpwrap_double_airy_ai :: Ptr CDouble -> CDouble -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_airy_ai/ /res/ /x/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_airy_ai_"
  arb_fpwrap_cdouble_airy_ai :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_airy_ai_prime/ /res/ /x/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_airy_ai_prime_"
  arb_fpwrap_double_airy_ai_prime :: Ptr CDouble -> CDouble -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_airy_ai_prime/ /res/ /x/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_airy_ai_prime_"
  arb_fpwrap_cdouble_airy_ai_prime :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_airy_bi/ /res/ /x/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_airy_bi_"
  arb_fpwrap_double_airy_bi :: Ptr CDouble -> CDouble -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_airy_bi/ /res/ /x/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_airy_bi_"
  arb_fpwrap_cdouble_airy_bi :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_airy_bi_prime/ /res/ /x/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_airy_bi_prime_"
  arb_fpwrap_double_airy_bi_prime :: Ptr CDouble -> CDouble -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_airy_bi_prime/ /res/ /x/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_airy_bi_prime_"
  arb_fpwrap_cdouble_airy_bi_prime :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_airy_ai_zero/ /res/ /n/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_airy_ai_zero_"
  arb_fpwrap_double_airy_ai_zero :: Ptr CDouble -> CULong -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_airy_ai_prime_zero/ /res/ /n/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_airy_ai_prime_zero_"
  arb_fpwrap_double_airy_ai_prime_zero :: Ptr CDouble -> CULong -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_airy_bi_zero/ /res/ /n/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_airy_bi_zero_"
  arb_fpwrap_double_airy_bi_zero :: Ptr CDouble -> CULong -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_airy_bi_prime_zero/ /res/ /n/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_airy_bi_prime_zero_"
  arb_fpwrap_double_airy_bi_prime_zero :: Ptr CDouble -> CULong -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_coulomb_f/ /res/ /l/ /eta/ /x/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_coulomb_f_"
  arb_fpwrap_double_coulomb_f :: Ptr CDouble -> CDouble -> CDouble -> CDouble -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_coulomb_f/ /res/ /l/ /eta/ /x/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_coulomb_f_"
  arb_fpwrap_cdouble_coulomb_f :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_coulomb_g/ /res/ /l/ /eta/ /x/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_coulomb_g_"
  arb_fpwrap_double_coulomb_g :: Ptr CDouble -> CDouble -> CDouble -> CDouble -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_coulomb_g/ /res/ /l/ /eta/ /x/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_coulomb_g_"
  arb_fpwrap_cdouble_coulomb_g :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_cdouble_coulomb_hpos/ /res/ /l/ /eta/ /x/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_coulomb_hpos_"
  arb_fpwrap_cdouble_coulomb_hpos :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_coulomb_hneg/ /res/ /l/ /eta/ /x/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_coulomb_hneg_"
  arb_fpwrap_cdouble_coulomb_hneg :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- Orthogonal polynomials ------------------------------------------------------

-- | /arb_fpwrap_double_chebyshev_t/ /res/ /n/ /x/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_chebyshev_t_"
  arb_fpwrap_double_chebyshev_t :: Ptr CDouble -> CDouble -> CDouble -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_chebyshev_t/ /res/ /n/ /x/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_chebyshev_t_"
  arb_fpwrap_cdouble_chebyshev_t :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_chebyshev_u/ /res/ /n/ /x/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_chebyshev_u_"
  arb_fpwrap_double_chebyshev_u :: Ptr CDouble -> CDouble -> CDouble -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_chebyshev_u/ /res/ /n/ /x/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_chebyshev_u_"
  arb_fpwrap_cdouble_chebyshev_u :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_jacobi_p/ /res/ /n/ /a/ /b/ /x/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_jacobi_p_"
  arb_fpwrap_double_jacobi_p :: Ptr CDouble -> CDouble -> CDouble -> CDouble -> CDouble -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_jacobi_p/ /res/ /n/ /a/ /b/ /x/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_jacobi_p_"
  arb_fpwrap_cdouble_jacobi_p :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_gegenbauer_c/ /res/ /n/ /m/ /x/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_gegenbauer_c_"
  arb_fpwrap_double_gegenbauer_c :: Ptr CDouble -> CDouble -> CDouble -> CDouble -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_gegenbauer_c/ /res/ /n/ /m/ /x/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_gegenbauer_c_"
  arb_fpwrap_cdouble_gegenbauer_c :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_laguerre_l/ /res/ /n/ /m/ /x/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_laguerre_l_"
  arb_fpwrap_double_laguerre_l :: Ptr CDouble -> CDouble -> CDouble -> CDouble -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_laguerre_l/ /res/ /n/ /m/ /x/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_laguerre_l_"
  arb_fpwrap_cdouble_laguerre_l :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_hermite_h/ /res/ /n/ /x/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_hermite_h_"
  arb_fpwrap_double_hermite_h :: Ptr CDouble -> CDouble -> CDouble -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_hermite_h/ /res/ /n/ /x/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_hermite_h_"
  arb_fpwrap_cdouble_hermite_h :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_legendre_p/ /res/ /n/ /m/ /x/ /type/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_legendre_p_"
  arb_fpwrap_double_legendre_p :: Ptr CDouble -> CDouble -> CDouble -> CDouble -> CInt -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_legendre_p/ /res/ /n/ /m/ /x/ /type/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_legendre_p_"
  arb_fpwrap_cdouble_legendre_p :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_legendre_q/ /res/ /n/ /m/ /x/ /type/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_legendre_q_"
  arb_fpwrap_double_legendre_q :: Ptr CDouble -> CDouble -> CDouble -> CDouble -> CInt -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_legendre_q/ /res/ /n/ /m/ /x/ /type/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_legendre_q_"
  arb_fpwrap_cdouble_legendre_q :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_legendre_root/ /res1/ /res2/ /n/ /k/ /flags/ 
--
-- Sets /res1/ to the index /k/ root of the Legendre polynomial \(P_n(x)\),
-- and simultaneously sets /res2/ to the corresponding weight for
-- Gauss-Legendre quadrature.
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_legendre_root_"
  arb_fpwrap_double_legendre_root :: Ptr CDouble -> Ptr CDouble -> CULong -> CULong -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_cdouble_spherical_y/ /res/ /n/ /m/ /x1/ /x2/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_spherical_y_"
  arb_fpwrap_cdouble_spherical_y :: Ptr (Complex CDouble) -> CLong -> CLong -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- Hypergeometric functions ----------------------------------------------------

-- | /arb_fpwrap_double_hypgeom_0f1/ /res/ /a/ /x/ /regularized/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_hypgeom_0f1_"
  arb_fpwrap_double_hypgeom_0f1 :: Ptr CDouble -> CDouble -> CDouble -> CInt -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_hypgeom_0f1/ /res/ /a/ /x/ /regularized/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_hypgeom_0f1_"
  arb_fpwrap_cdouble_hypgeom_0f1 :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_hypgeom_1f1/ /res/ /a/ /b/ /x/ /regularized/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_hypgeom_1f1_"
  arb_fpwrap_double_hypgeom_1f1 :: Ptr CDouble -> CDouble -> CDouble -> CDouble -> CInt -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_hypgeom_1f1/ /res/ /a/ /b/ /x/ /regularized/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_hypgeom_1f1_"
  arb_fpwrap_cdouble_hypgeom_1f1 :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_hypgeom_u/ /res/ /a/ /b/ /x/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_hypgeom_u_"
  arb_fpwrap_double_hypgeom_u :: Ptr CDouble -> CDouble -> CDouble -> CDouble -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_hypgeom_u/ /res/ /a/ /b/ /x/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_hypgeom_u_"
  arb_fpwrap_cdouble_hypgeom_u :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_hypgeom_2f1/ /res/ /a/ /b/ /c/ /x/ /regularized/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_hypgeom_2f1_"
  arb_fpwrap_double_hypgeom_2f1 :: Ptr CDouble -> CDouble -> CDouble -> CDouble -> CDouble -> CInt -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_hypgeom_2f1/ /res/ /a/ /b/ /c/ /x/ /regularized/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_hypgeom_2f1_"
  arb_fpwrap_cdouble_hypgeom_2f1 :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_double_hypgeom_pfq/ /res/ /a/ /p/ /b/ /q/ /z/ /regularized/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_hypgeom_pfq_"
  arb_fpwrap_double_hypgeom_pfq :: Ptr CDouble -> Ptr CDouble -> CLong -> Ptr CDouble -> CLong -> CDouble -> CInt -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_hypgeom_pfq/ /res/ /a/ /p/ /b/ /q/ /z/ /regularized/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_hypgeom_pfq_"
  arb_fpwrap_cdouble_hypgeom_pfq :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CLong -> Ptr (Complex CDouble) -> CLong -> Ptr (Complex CDouble) -> CInt -> CInt -> IO FpWrapReturn

-- Elliptic integrals, elliptic functions and modular forms --------------------

-- | /arb_fpwrap_double_agm/ /res/ /x/ /y/ /flags/ 
foreign import ccall "arb_fpwrap.h arb_fpwrap_double_agm_"
  arb_fpwrap_double_agm :: Ptr CDouble -> CDouble -> CDouble -> CInt -> IO FpWrapReturn
-- | /arb_fpwrap_cdouble_agm/ /res/ /x/ /y/ /flags/ 
--
-- Arithmetic-geometric mean.
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_agm_"
  arb_fpwrap_cdouble_agm :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_cdouble_elliptic_k/ /res/ /m/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_elliptic_k_"
  arb_fpwrap_cdouble_elliptic_k :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_cdouble_elliptic_e/ /res/ /m/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_elliptic_e_"
  arb_fpwrap_cdouble_elliptic_e :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_cdouble_elliptic_pi/ /res/ /n/ /m/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_elliptic_pi_"
  arb_fpwrap_cdouble_elliptic_pi :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_cdouble_elliptic_f/ /res/ /phi/ /m/ /pi/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_elliptic_f_"
  arb_fpwrap_cdouble_elliptic_f :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_cdouble_elliptic_e_inc/ /res/ /phi/ /m/ /pi/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_elliptic_e_inc_"
  arb_fpwrap_cdouble_elliptic_e_inc :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_cdouble_elliptic_pi_inc/ /res/ /n/ /phi/ /m/ /pi/ /flags/ 
--
-- Complete and incomplete elliptic integrals.
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_elliptic_pi_inc_"
  arb_fpwrap_cdouble_elliptic_pi_inc :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_cdouble_elliptic_rf/ /res/ /x/ /y/ /z/ /option/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_elliptic_rf_"
  arb_fpwrap_cdouble_elliptic_rf :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_cdouble_elliptic_rg/ /res/ /x/ /y/ /z/ /option/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_elliptic_rg_"
  arb_fpwrap_cdouble_elliptic_rg :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_cdouble_elliptic_rj/ /res/ /x/ /y/ /z/ /w/ /option/ /flags/ 
--
-- Carlson symmetric elliptic integrals.
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_elliptic_rj_"
  arb_fpwrap_cdouble_elliptic_rj :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_cdouble_elliptic_p/ /res/ /z/ /tau/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_elliptic_p_"
  arb_fpwrap_cdouble_elliptic_p :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_cdouble_elliptic_p_prime/ /res/ /z/ /tau/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_elliptic_p_prime_"
  arb_fpwrap_cdouble_elliptic_p_prime :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_cdouble_elliptic_inv_p/ /res/ /z/ /tau/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_elliptic_inv_p_"
  arb_fpwrap_cdouble_elliptic_inv_p :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_cdouble_elliptic_zeta/ /res/ /z/ /tau/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_elliptic_zeta_"
  arb_fpwrap_cdouble_elliptic_zeta :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_cdouble_elliptic_sigma/ /res/ /z/ /tau/ /flags/ 
--
-- Weierstrass elliptic functions.
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_elliptic_sigma_"
  arb_fpwrap_cdouble_elliptic_sigma :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_cdouble_jacobi_theta_1/ /res/ /z/ /tau/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_jacobi_theta_1_"
  arb_fpwrap_cdouble_jacobi_theta_1 :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_cdouble_jacobi_theta_2/ /res/ /z/ /tau/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_jacobi_theta_2_"
  arb_fpwrap_cdouble_jacobi_theta_2 :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_cdouble_jacobi_theta_3/ /res/ /z/ /tau/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_jacobi_theta_3_"
  arb_fpwrap_cdouble_jacobi_theta_3 :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_cdouble_jacobi_theta_4/ /res/ /z/ /tau/ /flags/ 
--
-- Jacobi theta functions.
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_jacobi_theta_4_"
  arb_fpwrap_cdouble_jacobi_theta_4 :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_cdouble_dedekind_eta/ /res/ /tau/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_dedekind_eta_"
  arb_fpwrap_cdouble_dedekind_eta :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_cdouble_modular_j/ /res/ /tau/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_modular_j_"
  arb_fpwrap_cdouble_modular_j :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_cdouble_modular_lambda/ /res/ /tau/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_modular_lambda_"
  arb_fpwrap_cdouble_modular_lambda :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn

-- | /arb_fpwrap_cdouble_modular_delta/ /res/ /tau/ /flags/ 
--
foreign import ccall "arb_fpwrap.h arb_fpwrap_cdouble_modular_delta_"
  arb_fpwrap_cdouble_modular_delta :: Ptr (Complex CDouble) -> Ptr (Complex CDouble) -> CInt -> IO FpWrapReturn



