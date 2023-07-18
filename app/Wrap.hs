module Wrap where

import System.IO.Unsafe
import Foreign.Ptr
import Foreign.C.Types
import Foreign.Marshal.Utils
import Foreign.Marshal.Alloc
import Foreign.Marshal.Array
import Foreign.Storable

import Data.Complex
import Data.Number.Flint.Arb.FpWrap

type CC = Complex CDouble
type CD = Complex Double

mainWrap = do
  let z = 0:+1 :: CD
  print $ cexp z
  print $ airy_ai  1
  print $ airy_ai' 1

cexp     = liftCCI arb_fpwrap_cdouble_exp
airy_ai  = liftDdI arb_fpwrap_double_airy_ai
airy_ai' = liftDdI arb_fpwrap_double_airy_ai_prime

modular_j      = liftCCI arb_fpwrap_cdouble_modular_j
modular_delta  = liftCCI arb_fpwrap_cdouble_modular_delta
modular_lambda = liftCCI arb_fpwrap_cdouble_modular_lambda
dedekind_eta   = liftCCI arb_fpwrap_cdouble_dedekind_eta

i = 0:+1
rho = (1 + i*sqrt 3)/2

-- -- real ------------------------------------------------------------------------

-- liftDI :: (Ptr CDouble -> CInt -> IO FpWrapReturn)
--        -> (Int -> Double)
-- liftDI f j = unsafePerformIO $ do
--   r <- malloc :: IO (Ptr CDouble)
--   flag <- f r (fromIntegral j) 0
--   res <- peek r
--   free r
--   return $ realToFrac res

-- liftDDI :: (CInt -> IO FpWrapReturn)
--        -> (Int -> ([Double], [Double]))
-- liftDDI f n = unsafePerformIO $ do
--   u <- mallocArray n :: IO (Ptr CDouble)
--   v <- mallocArray n :: IO (Ptr CDouble)
--   flag <- f u v 0
--   x <- peekArray n u
--   y <- peekArray n v
--   free u
--   free v
--   return $ (map realToFrac x, map realToFrac y)
  
liftDdI :: (Ptr CDouble -> CDouble -> CInt -> IO FpWrapReturn)
       -> (Double -> Double)
liftDdI f x = unsafePerformIO $ do
  r <- malloc :: IO (Ptr CDouble)
  flag <- f r (realToFrac x) 0
  res <- peek r
  free r
  return $ realToFrac res

-- liftDddI :: (Ptr CDouble -> CDouble -> CDouble -> CInt -> IO FpWrapReturn)
--        -> (Double -> Double -> Double)
-- liftDddI f x1 x2 = unsafePerformIO $ do
--   r <- malloc :: IO (Ptr CDouble)
--   flag <- f r (realToFrac x1) (realToFrac x2) 0
--   res <- peek r
--   free r
--   return $ realToFrac res

-- liftDdddI :: (Ptr CDouble -> CDouble -> CDouble -> CDouble -> CInt -> IO FpWrapReturn)
--        -> (Double -> Double -> Double -> Double)
-- liftDdddI f x1 x2 x3 = unsafePerformIO $ do
--   r <- malloc :: IO (Ptr CDouble)
--   flag <- f r (realToFrac x1) (realToFrac x2) (realToFrac x3) 0
--   res <- peek r
--   free r
--   return $ realToFrac res

-- liftDddddI :: (Ptr CDouble -> CDouble -> CDouble -> CDouble -> CDouble -> CInt -> IO FpWrapReturn)
--        -> (Double -> Double -> Double -> Double -> Double)
-- liftDddddI f x1 x2 x3 x4 = unsafePerformIO $ do
--   r <- malloc :: IO (Ptr CDouble)
--   flag <- f r (realToFrac x1) (realToFrac x2) (realToFrac x3) (realToFrac x4) 0
--   res <- peek r
--   free r
--   return $ realToFrac res

-- -- complex ---------------------------------------------------------------------

liftCCI :: (Ptr CC -> Ptr CC -> CInt -> IO FpWrapReturn)
        -> (Complex Double -> Complex Double)
liftCCI f (x:+y) = unsafePerformIO $ do
  r <- malloc :: IO (Ptr CC)
  p <- new (((realToFrac x) :+ (realToFrac y)) :: CC)
  flag <- f r p 0
  u:+v <- peek r
  free r
  free p
  return $ (realToFrac u) :+ (realToFrac v)

-- liftCCCI :: (Ptr CC -> Ptr CC -> Ptr CC -> CInt -> IO FpWrapReturn)
--         -> (CC -> CC -> CC)
-- liftCCCI f z1 z2 = unsafePerformIO $ do
--   r <- malloc :: IO (Ptr CC)
--   p1 <- new z1
--   p2 <- new z2
--   flag <- f r p1 p2 0
--   res <- peek r
--   free r
--   free p1
--   free p2
--   return $ res

-- liftCCCCI :: (Ptr CC -> Ptr CC-> Ptr CC-> Ptr CC -> CInt -> IO FpWrapReturn)
--         -> (CC -> CC -> CC -> CC)
-- liftCCCCI f z1 z2 z3 = unsafePerformIO $ do
--   r <- malloc :: IO (Ptr CC)
--   p1 <- new z1
--   p2 <- new z2
--   p3 <- new z3
--   flag <- f r p1 p2 p3 0
--   res <- peek r
--   free r
--   free p1
--   free p2
--   free p3
--   return $ res

-- liftCCCCCI :: (Ptr CC -> Ptr CC-> Ptr CC-> Ptr CC -> Ptr CC -> CInt -> IO FpWrapReturn)
--           -> (CC -> CC -> CC -> CC -> CC)
-- liftCCCCCI f z1 z2 z3 z4 = unsafePerformIO $ do
--   r <- malloc :: IO (Ptr CC)
--   p1 <- new z1
--   p2 <- new z2
--   p3 <- new z3
--   p4 <- new z4
--   flag <- f r p1 p2 p3 p4 0
--   res <- peek r
--   free r
--   free p1
--   free p2
--   free p3
--   free p4
--   return $ res
  
--------------------------------------------------------------------------------

-- lifting types
-- 
-- CCCCCI
-- CCCCI
-- CCCI
-- CCI
-- CI
-- DI
-- DDI
-- DdI
-- DddI
-- DdddI
-- DddddI

-- exp = liftDdI arb_fpwrap_double_exp_
-- exp = liftCCI arb_fpwrap_cdouble_exp_
-- expm1 = liftDdI arb_fpwrap_double_expm1_
-- expm1 = liftCCI arb_fpwrap_cdouble_expm1_
-- log = liftDdI arb_fpwrap_double_log_
-- log = liftCCI arb_fpwrap_cdouble_log_
-- log1p = liftDdI arb_fpwrap_double_log1p_
-- log1p = liftCCI arb_fpwrap_cdouble_log1p_
-- pow = liftDddI arb_fpwrap_double_pow_
-- pow = liftCCCI arb_fpwrap_cdouble_pow_
-- sqrt = liftDdI arb_fpwrap_double_sqrt_
-- sqrt = liftCCI arb_fpwrap_cdouble_sqrt_
-- rsqrt = liftDdI arb_fpwrap_double_rsqrt_
-- rsqrt = liftCCI arb_fpwrap_cdouble_rsqrt_
-- cbrt = liftDdI arb_fpwrap_double_cbrt_
-- cbrt = liftCCI arb_fpwrap_cdouble_cbrt_
-- sin = liftDdI arb_fpwrap_double_sin_
-- sin = liftCCI arb_fpwrap_cdouble_sin_
-- cos = liftDdI arb_fpwrap_double_cos_
-- cos = liftCCI arb_fpwrap_cdouble_cos_
-- tan = liftDdI arb_fpwrap_double_tan_
-- tan = liftCCI arb_fpwrap_cdouble_tan_
-- cot = liftDdI arb_fpwrap_double_cot_
-- cot = liftCCI arb_fpwrap_cdouble_cot_
-- sec = liftDdI arb_fpwrap_double_sec_
-- sec = liftCCI arb_fpwrap_cdouble_sec_
-- csc = liftDdI arb_fpwrap_double_csc_
-- csc = liftCCI arb_fpwrap_cdouble_csc_
-- sinc = liftDdI arb_fpwrap_double_sinc_
-- sinc = liftCCI arb_fpwrap_cdouble_sinc_
-- sin_pi = liftDdI arb_fpwrap_double_sin_pi_
-- sin_pi = liftCCI arb_fpwrap_cdouble_sin_pi_
-- cos_pi = liftDdI arb_fpwrap_double_cos_pi_
-- cos_pi = liftCCI arb_fpwrap_cdouble_cos_pi_
-- tan_pi = liftDdI arb_fpwrap_double_tan_pi_
-- tan_pi = liftCCI arb_fpwrap_cdouble_tan_pi_
-- cot_pi = liftDdI arb_fpwrap_double_cot_pi_
-- cot_pi = liftCCI arb_fpwrap_cdouble_cot_pi_
-- sinc_pi = liftDdI arb_fpwrap_double_sinc_pi_
-- sinc_pi = liftCCI arb_fpwrap_cdouble_sinc_pi_
-- asin = liftDdI arb_fpwrap_double_asin_
-- asin = liftCCI arb_fpwrap_cdouble_asin_
-- acos = liftDdI arb_fpwrap_double_acos_
-- acos = liftCCI arb_fpwrap_cdouble_acos_
-- atan = liftDdI arb_fpwrap_double_atan_
-- atan = liftCCI arb_fpwrap_cdouble_atan_
-- atan2 = liftDddI arb_fpwrap_double_atan2_
-- asinh = liftDdI arb_fpwrap_double_asinh_
-- asinh = liftCCI arb_fpwrap_cdouble_asinh_
-- acosh = liftDdI arb_fpwrap_double_acosh_
-- acosh = liftCCI arb_fpwrap_cdouble_acosh_
-- atanh = liftDdI arb_fpwrap_double_atanh_
-- atanh = liftCCI arb_fpwrap_cdouble_atanh_
-- lambertw = liftDdI arb_fpwrap_double_lambertw_
-- lambertw = liftCCI arb_fpwrap_cdouble_lambertw_
-- rising = liftDddI arb_fpwrap_double_rising_
-- rising = liftCCCI arb_fpwrap_cdouble_rising_
-- gamma = liftDdI arb_fpwrap_double_gamma_
-- gamma = liftCCI arb_fpwrap_cdouble_gamma_
-- rgamma = liftDdI arb_fpwrap_double_rgamma_
-- rgamma = liftCCI arb_fpwrap_cdouble_rgamma_
-- lgamma = liftDdI arb_fpwrap_double_lgamma_
-- lgamma = liftCCI arb_fpwrap_cdouble_lgamma_
-- digamma = liftDdI arb_fpwrap_double_digamma_
-- digamma = liftCCI arb_fpwrap_cdouble_digamma_
-- zeta = liftDdI arb_fpwrap_double_zeta_
-- zeta = liftCCI arb_fpwrap_cdouble_zeta_
-- hurwitz_zeta = liftDddI arb_fpwrap_double_hurwitz_zeta_
-- hurwitz_zeta = liftCCCI arb_fpwrap_cdouble_hurwitz_zeta_
-- lerch_phi = liftDdddI arb_fpwrap_double_lerch_phi_
-- lerch_phi = liftCCCCI arb_fpwrap_cdouble_lerch_phi_
-- barnes_g = liftDdI arb_fpwrap_double_barnes_g_
-- barnes_g = liftCCI arb_fpwrap_cdouble_barnes_g_
-- log_barnes_g = liftDdI arb_fpwrap_double_log_barnes_g_
-- log_barnes_g = liftCCI arb_fpwrap_cdouble_log_barnes_g_
-- polygamma = liftDddI arb_fpwrap_double_polygamma_
-- polygamma = liftCCCI arb_fpwrap_cdouble_polygamma_
-- polylog = liftDddI arb_fpwrap_double_polylog_
-- polylog = liftCCCI arb_fpwrap_cdouble_polylog_
-- dirichlet_eta = liftCCI arb_fpwrap_cdouble_dirichlet_eta_
-- riemann_xi = liftCCI arb_fpwrap_cdouble_riemann_xi_
-- hardy_theta = liftCCI arb_fpwrap_cdouble_hardy_theta_
-- hardy_z = liftCCI arb_fpwrap_cdouble_hardy_z_
-- zeta_zero = liftCI arb_fpwrap_cdouble_zeta_zero_
-- erf = liftDdI arb_fpwrap_double_erf_
-- erf = liftCCI arb_fpwrap_cdouble_erf_
-- erfc = liftDdI arb_fpwrap_double_erfc_
-- erfc = liftCCI arb_fpwrap_cdouble_erfc_
-- erfi = liftDdI arb_fpwrap_double_erfi_
-- erfi = liftCCI arb_fpwrap_cdouble_erfi_
-- erfinv = liftDdI arb_fpwrap_double_erfinv_
-- erfcinv = liftDdI arb_fpwrap_double_erfcinv_
-- fresnel_s = liftDdI arb_fpwrap_double_fresnel_s_
-- fresnel_s = liftCCI arb_fpwrap_cdouble_fresnel_s_
-- fresnel_c = liftDdI arb_fpwrap_double_fresnel_c_
-- fresnel_c = liftCCI arb_fpwrap_cdouble_fresnel_c_
-- gamma_upper = liftDddI arb_fpwrap_double_gamma_upper_
-- gamma_upper = liftCCCI arb_fpwrap_cdouble_gamma_upper_
-- gamma_lower = liftDddI arb_fpwrap_double_gamma_lower_
-- gamma_lower = liftCCCI arb_fpwrap_cdouble_gamma_lower_
-- beta_lower = liftDdddI arb_fpwrap_double_beta_lower_
-- beta_lower = liftCCCCI arb_fpwrap_cdouble_beta_lower_
-- exp_integral_e = liftDddI arb_fpwrap_double_exp_integral_e_
-- exp_integral_e = liftCCCI arb_fpwrap_cdouble_exp_integral_e_
-- exp_integral_ei = liftDdI arb_fpwrap_double_exp_integral_ei_
-- exp_integral_ei = liftCCI arb_fpwrap_cdouble_exp_integral_ei_
-- sin_integral = liftDdI arb_fpwrap_double_sin_integral_
-- sin_integral = liftCCI arb_fpwrap_cdouble_sin_integral_
-- cos_integral = liftDdI arb_fpwrap_double_cos_integral_
-- cos_integral = liftCCI arb_fpwrap_cdouble_cos_integral_
-- sinh_integral = liftDdI arb_fpwrap_double_sinh_integral_
-- sinh_integral = liftCCI arb_fpwrap_cdouble_sinh_integral_
-- cosh_integral = liftDdI arb_fpwrap_double_cosh_integral_
-- cosh_integral = liftCCI arb_fpwrap_cdouble_cosh_integral_
-- log_integral = liftDdI arb_fpwrap_double_log_integral_
-- log_integral = liftCCI arb_fpwrap_cdouble_log_integral_
-- dilog = liftDdI arb_fpwrap_double_dilog_
-- dilog = liftCCI arb_fpwrap_cdouble_dilog_
-- bessel_j = liftDddI arb_fpwrap_double_bessel_j_
-- bessel_j = liftCCCI arb_fpwrap_cdouble_bessel_j_
-- bessel_y = liftDddI arb_fpwrap_double_bessel_y_
-- bessel_y = liftCCCI arb_fpwrap_cdouble_bessel_y_
-- bessel_i = liftDddI arb_fpwrap_double_bessel_i_
-- bessel_i = liftCCCI arb_fpwrap_cdouble_bessel_i_
-- bessel_k = liftDddI arb_fpwrap_double_bessel_k_
-- bessel_k = liftCCCI arb_fpwrap_cdouble_bessel_k_
-- bessel_k_scaled = liftDddI arb_fpwrap_double_bessel_k_scaled_
-- bessel_k_scaled = liftCCCI arb_fpwrap_cdouble_bessel_k_scaled_
-- airy_ai = liftDdI arb_fpwrap_double_airy_ai_
-- airy_ai = liftCCI arb_fpwrap_cdouble_airy_ai_
-- airy_ai_prime = liftDdI arb_fpwrap_double_airy_ai_prime_
-- airy_ai_prime = liftCCI arb_fpwrap_cdouble_airy_ai_prime_
-- airy_bi = liftDdI arb_fpwrap_double_airy_bi_
-- airy_bi = liftCCI arb_fpwrap_cdouble_airy_bi_
-- airy_bi_prime = liftDdI arb_fpwrap_double_airy_bi_prime_
-- airy_bi_prime = liftCCI arb_fpwrap_cdouble_airy_bi_prime_
-- airy_ai_zero = liftDI arb_fpwrap_double_airy_ai_zero_
-- airy_ai_prime_zero = liftDI arb_fpwrap_double_airy_ai_prime_zero_
-- airy_bi_zero = liftDI arb_fpwrap_double_airy_bi_zero_
-- airy_bi_prime_zero = liftDI arb_fpwrap_double_airy_bi_prime_zero_
-- coulomb_f = liftDdddI arb_fpwrap_double_coulomb_f_
-- coulomb_f = liftCCCCI arb_fpwrap_cdouble_coulomb_f_
-- coulomb_g = liftDdddI arb_fpwrap_double_coulomb_g_
-- coulomb_g = liftCCCCI arb_fpwrap_cdouble_coulomb_g_
-- coulomb_hpos = liftCCCCI arb_fpwrap_cdouble_coulomb_hpos_
-- coulomb_hneg = liftCCCCI arb_fpwrap_cdouble_coulomb_hneg_
-- chebyshev_t = liftDddI arb_fpwrap_double_chebyshev_t_
-- chebyshev_t = liftCCCI arb_fpwrap_cdouble_chebyshev_t_
-- chebyshev_u = liftDddI arb_fpwrap_double_chebyshev_u_
-- chebyshev_u = liftCCCI arb_fpwrap_cdouble_chebyshev_u_
-- jacobi_p = liftDddddI arb_fpwrap_double_jacobi_p_
-- jacobi_p = liftCCCCCI arb_fpwrap_cdouble_jacobi_p_
-- gegenbauer_c = liftDdddI arb_fpwrap_double_gegenbauer_c_
-- gegenbauer_c = liftCCCCI arb_fpwrap_cdouble_gegenbauer_c_
-- laguerre_l = liftDdddI arb_fpwrap_double_laguerre_l_
-- laguerre_l = liftCCCCI arb_fpwrap_cdouble_laguerre_l_
-- hermite_h = liftDddI arb_fpwrap_double_hermite_h_
-- hermite_h = liftCCCI arb_fpwrap_cdouble_hermite_h_
-- legendre_p = liftDdddI arb_fpwrap_double_legendre_p_
-- legendre_p = liftCCCCI arb_fpwrap_cdouble_legendre_p_
-- legendre_q = liftDdddI arb_fpwrap_double_legendre_q_
-- legendre_q = liftCCCCI arb_fpwrap_cdouble_legendre_q_
-- legendre_root = liftDDI arb_fpwrap_double_legendre_root_
-- spherical_y = liftCCCI arb_fpwrap_cdouble_spherical_y_
-- hypgeom_0f1 = liftDddI arb_fpwrap_double_hypgeom_0f1_
-- hypgeom_0f1 = liftCCCI arb_fpwrap_cdouble_hypgeom_0f1_
-- hypgeom_1f1 = liftDdddI arb_fpwrap_double_hypgeom_1f1_
-- hypgeom_1f1 = liftCCCCI arb_fpwrap_cdouble_hypgeom_1f1_
-- hypgeom_u = liftDdddI arb_fpwrap_double_hypgeom_u_
-- hypgeom_u = liftCCCCI arb_fpwrap_cdouble_hypgeom_u_
-- hypgeom_2f1 = liftDddddI arb_fpwrap_double_hypgeom_2f1_
-- hypgeom_2f1 = liftCCCCCI arb_fpwrap_cdouble_hypgeom_2f1_
-- hypgeom_pfq = liftDdI arb_fpwrap_double_hypgeom_pfq_
-- hypgeom_pfq = liftCCI arb_fpwrap_cdouble_hypgeom_pfq_
-- agm = liftDddI arb_fpwrap_double_agm_
-- agm = liftCCCI arb_fpwrap_cdouble_agm_
-- elliptic_k = liftCCI arb_fpwrap_cdouble_elliptic_k_
-- elliptic_e = liftCCI arb_fpwrap_cdouble_elliptic_e_
-- elliptic_pi = liftCCCI arb_fpwrap_cdouble_elliptic_pi_
-- elliptic_f = liftCCCI arb_fpwrap_cdouble_elliptic_f_
-- elliptic_e_inc = liftCCCI arb_fpwrap_cdouble_elliptic_e_inc_
-- elliptic_pi_inc = liftCCCCI arb_fpwrap_cdouble_elliptic_pi_inc_
-- elliptic_rf = liftCCCCI arb_fpwrap_cdouble_elliptic_rf_
-- elliptic_rg = liftCCCCI arb_fpwrap_cdouble_elliptic_rg_
-- elliptic_rj = liftCCCCCI arb_fpwrap_cdouble_elliptic_rj_
-- elliptic_p = liftCCCI arb_fpwrap_cdouble_elliptic_p_
-- elliptic_p_prime = liftCCCI arb_fpwrap_cdouble_elliptic_p_prime_
-- elliptic_inv_p = liftCCCI arb_fpwrap_cdouble_elliptic_inv_p_
-- elliptic_zeta = liftCCCI arb_fpwrap_cdouble_elliptic_zeta_
-- elliptic_sigma = liftCCCI arb_fpwrap_cdouble_elliptic_sigma_
-- jacobi_theta_1 = liftCCCI arb_fpwrap_cdouble_jacobi_theta_1_
-- jacobi_theta_2 = liftCCCI arb_fpwrap_cdouble_jacobi_theta_2_
-- jacobi_theta_3 = liftCCCI arb_fpwrap_cdouble_jacobi_theta_3_
-- jacobi_theta_4 = liftCCCI arb_fpwrap_cdouble_jacobi_theta_4_
-- dedekind_eta = liftCCI arb_fpwrap_cdouble_dedekind_eta_
-- modular_j = liftCCI arb_fpwrap_cdouble_modular_j_
-- modular_lambda = liftCCI arb_fpwrap_cdouble_modular_lambda_
-- modular_delta = liftCCI arb_fpwrap_cdouble_modular_delta_
