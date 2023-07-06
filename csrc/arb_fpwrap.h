#ifndef CSRC_ARB_FPWRAP_H_
#define CSRC_ARB_FPWRAP_H_

#include <flint/arb_fpwrap.h>

// Haskell does not allow call by value for structure
//
// changed argument: complex_double -> complex_value *

int arb_fpwrap_double_exp_(double * res, double x, int flags);
int arb_fpwrap_cdouble_exp_(complex_double * res, complex_double * x, int flags);
int arb_fpwrap_double_expm1_(double * res, double x, int flags);
int arb_fpwrap_cdouble_expm1_(complex_double * res, complex_double * x, int flags);
int arb_fpwrap_double_log_(double * res, double x, int flags);
int arb_fpwrap_cdouble_log_(complex_double * res, complex_double * x, int flags);
int arb_fpwrap_double_log1p_(double * res, double x, int flags);
int arb_fpwrap_cdouble_log1p_(complex_double * res, complex_double * x, int flags);
int arb_fpwrap_double_pow_(double * res, double x, double y, int flags);
int arb_fpwrap_cdouble_pow_(complex_double * res, complex_double * x, complex_double * y, int flags);
int arb_fpwrap_double_sqrt_(double * res, double x, int flags);
int arb_fpwrap_cdouble_sqrt_(complex_double * res, complex_double * x, int flags);
int arb_fpwrap_double_rsqrt_(double * res, double x, int flags);
int arb_fpwrap_cdouble_rsqrt_(complex_double * res, complex_double * x, int flags);
int arb_fpwrap_double_cbrt_(double * res, double x, int flags);
int arb_fpwrap_cdouble_cbrt_(complex_double * res, complex_double * x, int flags);
int arb_fpwrap_double_sin_(double * res, double x, int flags);
int arb_fpwrap_cdouble_sin_(complex_double * res, complex_double * x, int flags);
int arb_fpwrap_double_cos_(double * res, double x, int flags);
int arb_fpwrap_cdouble_cos_(complex_double * res, complex_double * x, int flags);
int arb_fpwrap_double_tan_(double * res, double x, int flags);
int arb_fpwrap_cdouble_tan_(complex_double * res, complex_double * x, int flags);
int arb_fpwrap_double_cot_(double * res, double x, int flags);
int arb_fpwrap_cdouble_cot_(complex_double * res, complex_double * x, int flags);
int arb_fpwrap_double_sec_(double * res, double x, int flags);
int arb_fpwrap_cdouble_sec_(complex_double * res, complex_double * x, int flags);
int arb_fpwrap_double_csc_(double * res, double x, int flags);
int arb_fpwrap_cdouble_csc_(complex_double * res, complex_double * x, int flags);
int arb_fpwrap_double_sinc_(double * res, double x, int flags);
int arb_fpwrap_cdouble_sinc_(complex_double * res, complex_double * x, int flags);
int arb_fpwrap_double_sin_pi_(double * res, double x, int flags);
int arb_fpwrap_cdouble_sin_pi_(complex_double * res, complex_double * x, int flags);
int arb_fpwrap_double_cos_pi_(double * res, double x, int flags);
int arb_fpwrap_cdouble_cos_pi_(complex_double * res, complex_double * x, int flags);
int arb_fpwrap_double_tan_pi_(double * res, double x, int flags);
int arb_fpwrap_cdouble_tan_pi_(complex_double * res, complex_double * x, int flags);
int arb_fpwrap_double_cot_pi_(double * res, double x, int flags);
int arb_fpwrap_cdouble_cot_pi_(complex_double * res, complex_double * x, int flags);
int arb_fpwrap_double_sinc_pi_(double * res, double x, int flags);
int arb_fpwrap_cdouble_sinc_pi_(complex_double * res, complex_double * x, int flags);
int arb_fpwrap_double_asin_(double * res, double x, int flags);
int arb_fpwrap_cdouble_asin_(complex_double * res, complex_double * x, int flags);
int arb_fpwrap_double_acos_(double * res, double x, int flags);
int arb_fpwrap_cdouble_acos_(complex_double * res, complex_double * x, int flags);
int arb_fpwrap_double_atan_(double * res, double x, int flags);
int arb_fpwrap_cdouble_atan_(complex_double * res, complex_double * x, int flags);
int arb_fpwrap_double_atan2_(double * res, double x1, double x2, int flags);
int arb_fpwrap_double_asinh_(double * res, double x, int flags);
int arb_fpwrap_cdouble_asinh_(complex_double * res, complex_double * x, int flags);
int arb_fpwrap_double_acosh_(double * res, double x, int flags);
int arb_fpwrap_cdouble_acosh_(complex_double * res, complex_double * x, int flags);
int arb_fpwrap_double_atanh_(double * res, double x, int flags);
int arb_fpwrap_cdouble_atanh_(complex_double * res, complex_double * x, int flags);
int arb_fpwrap_double_lambertw_(double * res, double x, slong branch, int flags);
int arb_fpwrap_cdouble_lambertw_(complex_double * res, complex_double * x, slong branch, int flags);
int arb_fpwrap_double_rising_(double * res, double x, double n, int flags);
int arb_fpwrap_cdouble_rising_(complex_double * res, complex_double * x, complex_double * n, int flags);
int arb_fpwrap_double_gamma_(double * res, double x, int flags);
int arb_fpwrap_cdouble_gamma_(complex_double * res, complex_double * x, int flags);
int arb_fpwrap_double_rgamma_(double * res, double x, int flags);
int arb_fpwrap_cdouble_rgamma_(complex_double * res, complex_double * x, int flags);
int arb_fpwrap_double_lgamma_(double * res, double x, int flags);
int arb_fpwrap_cdouble_lgamma_(complex_double * res, complex_double * x, int flags);
int arb_fpwrap_double_digamma_(double * res, double x, int flags);
int arb_fpwrap_cdouble_digamma_(complex_double * res, complex_double * x, int flags);
int arb_fpwrap_double_zeta_(double * res, double x, int flags);
int arb_fpwrap_cdouble_zeta_(complex_double * res, complex_double * x, int flags);
int arb_fpwrap_double_hurwitz_zeta_(double * res, double s, double z, int flags);
int arb_fpwrap_cdouble_hurwitz_zeta_(complex_double * res, complex_double * s, complex_double * z, int flags);
int arb_fpwrap_double_lerch_phi_(double * res, double z, double s, double a, int flags);
int arb_fpwrap_cdouble_lerch_phi_(complex_double * res, complex_double * z, complex_double * s, complex_double * a, int flags);
int arb_fpwrap_double_barnes_g_(double * res, double x, int flags);
int arb_fpwrap_cdouble_barnes_g_(complex_double * res, complex_double * x, int flags);
int arb_fpwrap_double_log_barnes_g_(double * res, double x, int flags);
int arb_fpwrap_cdouble_log_barnes_g_(complex_double * res, complex_double * x, int flags);
int arb_fpwrap_double_polygamma_(double * res, double s, double z, int flags);
int arb_fpwrap_cdouble_polygamma_(complex_double * res, complex_double * s, complex_double * z, int flags);
int arb_fpwrap_double_polylog_(double * res, double s, double z, int flags);
int arb_fpwrap_cdouble_polylog_(complex_double * res, complex_double * s, complex_double * z, int flags);
int arb_fpwrap_cdouble_dirichlet_eta_(complex_double * res, complex_double * s, int flags);
int arb_fpwrap_cdouble_riemann_xi_(complex_double * res, complex_double * s, int flags);
int arb_fpwrap_cdouble_hardy_theta_(complex_double * res, complex_double * z, int flags);
int arb_fpwrap_cdouble_hardy_z_(complex_double * res, complex_double * z, int flags);
int arb_fpwrap_cdouble_zeta_zero_(complex_double * res, ulong n, int flags);
int arb_fpwrap_double_erf_(double * res, double x, int flags);
int arb_fpwrap_cdouble_erf_(complex_double * res, complex_double * x, int flags);
int arb_fpwrap_double_erfc_(double * res, double x, int flags);
int arb_fpwrap_cdouble_erfc_(complex_double * res, complex_double * x, int flags);
int arb_fpwrap_double_erfi_(double * res, double x, int flags);
int arb_fpwrap_cdouble_erfi_(complex_double * res, complex_double * x, int flags);
int arb_fpwrap_double_erfinv_(double * res, double x, int flags);
int arb_fpwrap_double_erfcinv_(double * res, double x, int flags);
int arb_fpwrap_double_fresnel_s_(double * res, double x, int normalized, int flags);
int arb_fpwrap_cdouble_fresnel_s_(complex_double * res, complex_double * x, int normalized, int flags);
int arb_fpwrap_double_fresnel_c_(double * res, double x, int normalized, int flags);
int arb_fpwrap_cdouble_fresnel_c_(complex_double * res, complex_double * x, int normalized, int flags);
int arb_fpwrap_double_gamma_upper_(double * res, double s, double z, int regularized, int flags);
int arb_fpwrap_cdouble_gamma_upper_(complex_double * res, complex_double * s, complex_double * z, int regularized, int flags);
int arb_fpwrap_double_gamma_lower_(double * res, double s, double z, int regularized, int flags);
int arb_fpwrap_cdouble_gamma_lower_(complex_double * res, complex_double * s, complex_double * z, int regularized, int flags);
int arb_fpwrap_double_beta_lower_(double * res, double a, double b, double z, int regularized, int flags);
int arb_fpwrap_cdouble_beta_lower_(complex_double * res, complex_double * a, complex_double * b, complex_double * z, int regularized, int flags);
int arb_fpwrap_double_exp_integral_e_(double * res, double s, double z, int flags);
int arb_fpwrap_cdouble_exp_integral_e_(complex_double * res, complex_double * s, complex_double * z, int flags);
int arb_fpwrap_double_exp_integral_ei_(double * res, double x, int flags);
int arb_fpwrap_cdouble_exp_integral_ei_(complex_double * res, complex_double * x, int flags);
int arb_fpwrap_double_sin_integral_(double * res, double x, int flags);
int arb_fpwrap_cdouble_sin_integral_(complex_double * res, complex_double * x, int flags);
int arb_fpwrap_double_cos_integral_(double * res, double x, int flags);
int arb_fpwrap_cdouble_cos_integral_(complex_double * res, complex_double * x, int flags);
int arb_fpwrap_double_sinh_integral_(double * res, double x, int flags);
int arb_fpwrap_cdouble_sinh_integral_(complex_double * res, complex_double * x, int flags);
int arb_fpwrap_double_cosh_integral_(double * res, double x, int flags);
int arb_fpwrap_cdouble_cosh_integral_(complex_double * res, complex_double * x, int flags);
int arb_fpwrap_double_log_integral_(double * res, double x, int offset, int flags);
int arb_fpwrap_cdouble_log_integral_(complex_double * res, complex_double * x, int offset, int flags);
int arb_fpwrap_double_dilog_(double * res, double x, int flags);
int arb_fpwrap_cdouble_dilog_(complex_double * res, complex_double * x, int flags);
int arb_fpwrap_double_bessel_j_(double * res, double nu, double x, int flags);
int arb_fpwrap_cdouble_bessel_j_(complex_double * res, complex_double * nu, complex_double * x, int flags);
int arb_fpwrap_double_bessel_y_(double * res, double nu, double x, int flags);
int arb_fpwrap_cdouble_bessel_y_(complex_double * res, complex_double * nu, complex_double * x, int flags);
int arb_fpwrap_double_bessel_i_(double * res, double nu, double x, int flags);
int arb_fpwrap_cdouble_bessel_i_(complex_double * res, complex_double * nu, complex_double * x, int flags);
int arb_fpwrap_double_bessel_k_(double * res, double nu, double x, int flags);
int arb_fpwrap_cdouble_bessel_k_(complex_double * res, complex_double * nu, complex_double * x, int flags);
int arb_fpwrap_double_bessel_k_scaled_(double * res, double nu, double x, int flags);
int arb_fpwrap_cdouble_bessel_k_scaled_(complex_double * res, complex_double * nu, complex_double * x, int flags);
int arb_fpwrap_double_airy_ai_(double * res, double x, int flags);
int arb_fpwrap_cdouble_airy_ai_(complex_double * res, complex_double * x, int flags);
int arb_fpwrap_double_airy_ai_prime_(double * res, double x, int flags);
int arb_fpwrap_cdouble_airy_ai_prime_(complex_double * res, complex_double * x, int flags);
int arb_fpwrap_double_airy_bi_(double * res, double x, int flags);
int arb_fpwrap_cdouble_airy_bi_(complex_double * res, complex_double * x, int flags);
int arb_fpwrap_double_airy_bi_prime_(double * res, double x, int flags);
int arb_fpwrap_cdouble_airy_bi_prime_(complex_double * res, complex_double * x, int flags);
int arb_fpwrap_double_airy_ai_zero_(double * res, ulong n, int flags);
int arb_fpwrap_double_airy_ai_prime_zero_(double * res, ulong n, int flags);
int arb_fpwrap_double_airy_bi_zero_(double * res, ulong n, int flags);
int arb_fpwrap_double_airy_bi_prime_zero_(double * res, ulong n, int flags);
int arb_fpwrap_double_coulomb_f_(double * res, double l, double eta, double x, int flags);
int arb_fpwrap_cdouble_coulomb_f_(complex_double * res, complex_double * l, complex_double * eta, complex_double * x, int flags);
int arb_fpwrap_double_coulomb_g_(double * res, double l, double eta, double x, int flags);
int arb_fpwrap_cdouble_coulomb_g_(complex_double * res, complex_double * l, complex_double * eta, complex_double * x, int flags);
int arb_fpwrap_cdouble_coulomb_hpos_(complex_double * res, complex_double * l, complex_double * eta, complex_double * x, int flags);
int arb_fpwrap_cdouble_coulomb_hneg_(complex_double * res, complex_double * l, complex_double * eta, complex_double * x, int flags);
int arb_fpwrap_double_chebyshev_t_(double * res, double n, double x, int flags);
int arb_fpwrap_cdouble_chebyshev_t_(complex_double * res, complex_double * n, complex_double * x, int flags);
int arb_fpwrap_double_chebyshev_u_(double * res, double n, double x, int flags);
int arb_fpwrap_cdouble_chebyshev_u_(complex_double * res, complex_double * n, complex_double * x, int flags);
int arb_fpwrap_double_jacobi_p_(double * res, double n, double a, double b, double x, int flags);
int arb_fpwrap_cdouble_jacobi_p_(complex_double * res, complex_double * n, complex_double * a, complex_double * b, complex_double * x, int flags);
int arb_fpwrap_double_gegenbauer_c_(double * res, double n, double m, double x, int flags);
int arb_fpwrap_cdouble_gegenbauer_c_(complex_double * res, complex_double * n, complex_double * m, complex_double * x, int flags);
int arb_fpwrap_double_laguerre_l_(double * res, double n, double m, double x, int flags);
int arb_fpwrap_cdouble_laguerre_l_(complex_double * res, complex_double * n, complex_double * m, complex_double * x, int flags);
int arb_fpwrap_double_hermite_h_(double * res, double n, double x, int flags);
int arb_fpwrap_cdouble_hermite_h_(complex_double * res, complex_double * n, complex_double * x, int flags);
int arb_fpwrap_double_legendre_p_(double * res, double n, double m, double x, int type, int flags);
int arb_fpwrap_cdouble_legendre_p_(complex_double * res, complex_double * n, complex_double * m, complex_double * x, int type, int flags);
int arb_fpwrap_double_legendre_q_(double * res, double n, double m, double x, int type, int flags);
int arb_fpwrap_cdouble_legendre_q_(complex_double * res, complex_double * n, complex_double * m, complex_double * x, int type, int flags);
int arb_fpwrap_double_legendre_root_(double * res1, double * res2, ulong n, ulong k, int flags);
int arb_fpwrap_cdouble_spherical_y_(complex_double * res, slong n, slong m, complex_double * x1, complex_double * x2, int flags);
int arb_fpwrap_double_hypgeom_0f1_(double * res, double a, double x, int regularized, int flags);
int arb_fpwrap_cdouble_hypgeom_0f1_(complex_double * res, complex_double * a, complex_double * x, int regularized, int flags);
int arb_fpwrap_double_hypgeom_1f1_(double * res, double a, double b, double x, int regularized, int flags);
int arb_fpwrap_cdouble_hypgeom_1f1_(complex_double * res, complex_double * a, complex_double * b, complex_double * x, int regularized, int flags);
int arb_fpwrap_double_hypgeom_u_(double * res, double a, double b, double x, int flags);
int arb_fpwrap_cdouble_hypgeom_u_(complex_double * res, complex_double * a, complex_double * b, complex_double * x, int flags);
int arb_fpwrap_double_hypgeom_2f1_(double * res, double a, double b, double c, double x, int regularized, int flags);
int arb_fpwrap_cdouble_hypgeom_2f1_(complex_double * res, complex_double * a, complex_double * b, complex_double * c, complex_double * x, int regularized, int flags);
int arb_fpwrap_double_hypgeom_pfq_(double * res, const double * a, slong p, const double * b, slong q, double z, int regularized, int flags);
int arb_fpwrap_cdouble_hypgeom_pfq_(complex_double * res, const complex_double * a, slong p, const complex_double * b, slong q, complex_double * z, int regularized, int flags);
int arb_fpwrap_double_agm_(double * res, double x, double y, int flags);
int arb_fpwrap_cdouble_agm_(complex_double * res, complex_double * x, complex_double * y, int flags);
int arb_fpwrap_cdouble_elliptic_k_(complex_double * res, complex_double * m, int flags);
int arb_fpwrap_cdouble_elliptic_e_(complex_double * res, complex_double * m, int flags);
int arb_fpwrap_cdouble_elliptic_pi_(complex_double * res, complex_double * n, complex_double * m, int flags);
int arb_fpwrap_cdouble_elliptic_f_(complex_double * res, complex_double * phi, complex_double * m, int pi, int flags);
int arb_fpwrap_cdouble_elliptic_e_inc_(complex_double * res, complex_double * phi, complex_double * m, int pi, int flags);
int arb_fpwrap_cdouble_elliptic_pi_inc_(complex_double * res, complex_double * n, complex_double * phi, complex_double * m, int pi, int flags);
int arb_fpwrap_cdouble_elliptic_rf_(complex_double * res, complex_double * x, complex_double * y, complex_double * z, int option, int flags);
int arb_fpwrap_cdouble_elliptic_rg_(complex_double * res, complex_double * x, complex_double * y, complex_double * z, int option, int flags);
int arb_fpwrap_cdouble_elliptic_rj_(complex_double * res, complex_double * x, complex_double * y, complex_double * z, complex_double * w, int option, int flags);
int arb_fpwrap_cdouble_elliptic_p_(complex_double * res, complex_double * z, complex_double * tau, int flags);
int arb_fpwrap_cdouble_elliptic_p_prime_(complex_double * res, complex_double * z, complex_double * tau, int flags);
int arb_fpwrap_cdouble_elliptic_inv_p_(complex_double * res, complex_double * z, complex_double * tau, int flags);
int arb_fpwrap_cdouble_elliptic_zeta_(complex_double * res, complex_double * z, complex_double * tau, int flags);
int arb_fpwrap_cdouble_elliptic_sigma_(complex_double * res, complex_double * z, complex_double * tau, int flags);
int arb_fpwrap_cdouble_jacobi_theta_1_(complex_double * res, complex_double * z, complex_double * tau, int flags);
int arb_fpwrap_cdouble_jacobi_theta_2_(complex_double * res, complex_double * z, complex_double * tau, int flags);
int arb_fpwrap_cdouble_jacobi_theta_3_(complex_double * res, complex_double * z, complex_double * tau, int flags);
int arb_fpwrap_cdouble_jacobi_theta_4_(complex_double * res, complex_double * z, complex_double * tau, int flags);
int arb_fpwrap_cdouble_dedekind_eta_(complex_double * res, complex_double * tau, int flags);
int arb_fpwrap_cdouble_modular_j_(complex_double * res, complex_double * tau, int flags);
int arb_fpwrap_cdouble_modular_lambda_(complex_double * res, complex_double * tau, int flags);
int arb_fpwrap_cdouble_modular_delta_(complex_double * res, complex_double * tau, int flags);

#endif // CSRC_ARB_FPWRAP_H_