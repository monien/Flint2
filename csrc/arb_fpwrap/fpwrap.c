#include <flint/arb_fpwrap.h>

// Haskell does not allow call by value for structure
//
// changed argument: complex_double -> complex_value *

int arb_fpwrap_double_exp_(double * res, double x, int flags) {
  return arb_fpwrap_double_exp(res, x, flags);
};

int arb_fpwrap_cdouble_exp_(complex_double * res, complex_double * x, int flags) {
  return arb_fpwrap_cdouble_exp(res, *x, flags);
};

int arb_fpwrap_double_expm1_(double * res, double x, int flags) {
  return arb_fpwrap_double_expm1(res, x, flags);
};

int arb_fpwrap_cdouble_expm1_(complex_double * res, complex_double * x, int flags) {
  return arb_fpwrap_cdouble_expm1(res, *x, flags);
};

int arb_fpwrap_double_log_(double * res, double x, int flags) {
  return arb_fpwrap_double_log(res, x, flags);
};

int arb_fpwrap_cdouble_log_(complex_double * res, complex_double * x, int flags) {
  return arb_fpwrap_cdouble_log(res, *x, flags);
};

int arb_fpwrap_double_log1p_(double * res, double x, int flags) {
  return arb_fpwrap_double_log1p(res, x, flags);
};

int arb_fpwrap_cdouble_log1p_(complex_double * res, complex_double * x, int flags) {
  return arb_fpwrap_cdouble_log1p(res, *x, flags);
};

int arb_fpwrap_double_pow_(double * res, double x, double y, int flags) {
  return arb_fpwrap_double_pow(res, x, y, flags);
};

int arb_fpwrap_cdouble_pow_(complex_double * res, complex_double * x, complex_double * y, int flags) {
  return arb_fpwrap_cdouble_pow(res, *x, *y, flags);
};

int arb_fpwrap_double_sqrt_(double * res, double x, int flags) {
  return arb_fpwrap_double_sqrt(res, x, flags);
};

int arb_fpwrap_cdouble_sqrt_(complex_double * res, complex_double * x, int flags) {
  return arb_fpwrap_cdouble_sqrt(res, *x, flags);
};

int arb_fpwrap_double_rsqrt_(double * res, double x, int flags) {
  return arb_fpwrap_double_rsqrt(res, x, flags);
};

int arb_fpwrap_cdouble_rsqrt_(complex_double * res, complex_double * x, int flags) {
  return arb_fpwrap_cdouble_rsqrt(res, *x, flags);
};

int arb_fpwrap_double_cbrt_(double * res, double x, int flags) {
  return arb_fpwrap_double_cbrt(res, x, flags);
};

int arb_fpwrap_cdouble_cbrt_(complex_double * res, complex_double * x, int flags) {
  return arb_fpwrap_cdouble_cbrt(res, *x, flags);
};

int arb_fpwrap_double_sin_(double * res, double x, int flags) {
  return arb_fpwrap_double_sin(res, x, flags);
};

int arb_fpwrap_cdouble_sin_(complex_double * res, complex_double * x, int flags) {
  return arb_fpwrap_cdouble_sin(res, *x, flags);
};

int arb_fpwrap_double_cos_(double * res, double x, int flags) {
  return arb_fpwrap_double_cos(res, x, flags);
};

int arb_fpwrap_cdouble_cos_(complex_double * res, complex_double * x, int flags) {
  return arb_fpwrap_cdouble_cos(res, *x, flags);
};

int arb_fpwrap_double_tan_(double * res, double x, int flags) {
  return arb_fpwrap_double_tan(res, x, flags);
};

int arb_fpwrap_cdouble_tan_(complex_double * res, complex_double * x, int flags) {
  return arb_fpwrap_cdouble_tan(res, *x, flags);
};

int arb_fpwrap_double_cot_(double * res, double x, int flags) {
  return arb_fpwrap_double_cot(res, x, flags);
};

int arb_fpwrap_cdouble_cot_(complex_double * res, complex_double * x, int flags) {
  return arb_fpwrap_cdouble_cot(res, *x, flags);
};

int arb_fpwrap_double_sec_(double * res, double x, int flags) {
  return arb_fpwrap_double_sec(res, x, flags);
};

int arb_fpwrap_cdouble_sec_(complex_double * res, complex_double * x, int flags) {
  return arb_fpwrap_cdouble_sec(res, *x, flags);
};

int arb_fpwrap_double_csc_(double * res, double x, int flags) {
  return arb_fpwrap_double_csc(res, x, flags);
};

int arb_fpwrap_cdouble_csc_(complex_double * res, complex_double * x, int flags) {
  return arb_fpwrap_cdouble_csc(res, *x, flags);
};

int arb_fpwrap_double_sinc_(double * res, double x, int flags) {
  return arb_fpwrap_double_sinc(res, x, flags);
};

int arb_fpwrap_cdouble_sinc_(complex_double * res, complex_double * x, int flags) {
  return arb_fpwrap_cdouble_sinc(res, *x, flags);
};

int arb_fpwrap_double_sin_pi_(double * res, double x, int flags) {
  return arb_fpwrap_double_sin_pi(res, x, flags);
};

int arb_fpwrap_cdouble_sin_pi_(complex_double * res, complex_double * x, int flags) {
  return arb_fpwrap_cdouble_sin_pi(res, *x, flags);
};

int arb_fpwrap_double_cos_pi_(double * res, double x, int flags) {
  return arb_fpwrap_double_cos_pi(res, x, flags);
};

int arb_fpwrap_cdouble_cos_pi_(complex_double * res, complex_double * x, int flags) {
  return arb_fpwrap_cdouble_cos_pi(res, *x, flags);
};

int arb_fpwrap_double_tan_pi_(double * res, double x, int flags) {
  return arb_fpwrap_double_tan_pi(res, x, flags);
};

int arb_fpwrap_cdouble_tan_pi_(complex_double * res, complex_double * x, int flags) {
  return arb_fpwrap_cdouble_tan_pi(res, *x, flags);
};

int arb_fpwrap_double_cot_pi_(double * res, double x, int flags) {
  return arb_fpwrap_double_cot_pi(res, x, flags);
};

int arb_fpwrap_cdouble_cot_pi_(complex_double * res, complex_double * x, int flags) {
  return arb_fpwrap_cdouble_cot_pi(res, *x, flags);
};

int arb_fpwrap_double_sinc_pi_(double * res, double x, int flags) {
  return arb_fpwrap_double_sinc_pi(res, x, flags);
};

int arb_fpwrap_cdouble_sinc_pi_(complex_double * res, complex_double * x, int flags) {
  return arb_fpwrap_cdouble_sinc_pi(res, *x, flags);
};

int arb_fpwrap_double_asin_(double * res, double x, int flags) {
  return arb_fpwrap_double_asin(res, x, flags);
};

int arb_fpwrap_cdouble_asin_(complex_double * res, complex_double * x, int flags) {
  return arb_fpwrap_cdouble_asin(res, *x, flags);
};

int arb_fpwrap_double_acos_(double * res, double x, int flags) {
  return arb_fpwrap_double_acos(res, x, flags);
};

int arb_fpwrap_cdouble_acos_(complex_double * res, complex_double * x, int flags) {
  return arb_fpwrap_cdouble_acos(res, *x, flags);
};

int arb_fpwrap_double_atan_(double * res, double x, int flags) {
  return arb_fpwrap_double_atan(res, x, flags);
};

int arb_fpwrap_cdouble_atan_(complex_double * res, complex_double * x, int flags) {
  return arb_fpwrap_cdouble_atan(res, *x, flags);
};

int arb_fpwrap_double_atan2_(double * res, double x1, double x2, int flags) {
  return arb_fpwrap_double_atan2(res, x1, x2, flags);
};

int arb_fpwrap_double_asinh_(double * res, double x, int flags) {
  return arb_fpwrap_double_asinh(res, x, flags);
};

int arb_fpwrap_cdouble_asinh_(complex_double * res, complex_double * x, int flags) {
  return arb_fpwrap_cdouble_asinh(res, *x, flags);
};

int arb_fpwrap_double_acosh_(double * res, double x, int flags) {
  return arb_fpwrap_double_acosh(res, x, flags);
};

int arb_fpwrap_cdouble_acosh_(complex_double * res, complex_double * x, int flags) {
  return arb_fpwrap_cdouble_acosh(res, *x, flags);
};

int arb_fpwrap_double_atanh_(double * res, double x, int flags) {
  return arb_fpwrap_double_atanh(res, x, flags);
};

int arb_fpwrap_cdouble_atanh_(complex_double * res, complex_double * x, int flags) {
  return arb_fpwrap_cdouble_atanh(res, *x, flags);
};

int arb_fpwrap_double_lambertw_(double * res, double x, slong branch, int flags) {
  return arb_fpwrap_double_lambertw(res, x, branch, flags);
};

int arb_fpwrap_cdouble_lambertw_(complex_double * res, complex_double * x, slong branch, int flags) {
  return arb_fpwrap_cdouble_lambertw(res, *x, branch, flags);
};

int arb_fpwrap_double_rising_(double * res, double x, double n, int flags) {
  return arb_fpwrap_double_rising(res, x, n, flags);
};

int arb_fpwrap_cdouble_rising_(complex_double * res, complex_double * x, complex_double * n, int flags) {
  return arb_fpwrap_cdouble_rising(res, *x, *n, flags);
};

int arb_fpwrap_double_gamma_(double * res, double x, int flags) {
  return arb_fpwrap_double_gamma(res, x, flags);
};

int arb_fpwrap_cdouble_gamma_(complex_double * res, complex_double * x, int flags) {
  return arb_fpwrap_cdouble_gamma(res, *x, flags);
};

int arb_fpwrap_double_rgamma_(double * res, double x, int flags) {
  return arb_fpwrap_double_rgamma(res, x, flags);
};

int arb_fpwrap_cdouble_rgamma_(complex_double * res, complex_double * x, int flags) {
  return arb_fpwrap_cdouble_rgamma(res, *x, flags);
};

int arb_fpwrap_double_lgamma_(double * res, double x, int flags) {
  return arb_fpwrap_double_lgamma(res, x, flags);
};

int arb_fpwrap_cdouble_lgamma_(complex_double * res, complex_double * x, int flags) {
  return arb_fpwrap_cdouble_lgamma(res, *x, flags);
};

int arb_fpwrap_double_digamma_(double * res, double x, int flags) {
  return arb_fpwrap_double_digamma(res, x, flags);
};

int arb_fpwrap_cdouble_digamma_(complex_double * res, complex_double * x, int flags) {
  return arb_fpwrap_cdouble_digamma(res, *x, flags);
};

int arb_fpwrap_double_zeta_(double * res, double x, int flags) {
  return arb_fpwrap_double_zeta(res, x, flags);
};

int arb_fpwrap_cdouble_zeta_(complex_double * res, complex_double * x, int flags) {
  return arb_fpwrap_cdouble_zeta(res, *x, flags);
};

int arb_fpwrap_double_hurwitz_zeta_(double * res, double s, double z, int flags) {
  return arb_fpwrap_double_hurwitz_zeta(res, s, z, flags);
};

int arb_fpwrap_cdouble_hurwitz_zeta_(complex_double * res, complex_double * s, complex_double * z, int flags) {
  return arb_fpwrap_cdouble_hurwitz_zeta(res, *s, *z, flags);
};

int arb_fpwrap_double_lerch_phi_(double * res, double z, double s, double a, int flags) {
  return arb_fpwrap_double_lerch_phi(res, z, s, a, flags);
};

int arb_fpwrap_cdouble_lerch_phi_(complex_double * res, complex_double * z, complex_double * s, complex_double * a, int flags) {
  return arb_fpwrap_cdouble_lerch_phi(res, *z, *s, *a, flags);
};

int arb_fpwrap_double_barnes_g_(double * res, double x, int flags) {
  return arb_fpwrap_double_barnes_g(res, x, flags);
};

int arb_fpwrap_cdouble_barnes_g_(complex_double * res, complex_double * x, int flags) {
  return arb_fpwrap_cdouble_barnes_g(res, *x, flags);
};

int arb_fpwrap_double_log_barnes_g_(double * res, double x, int flags) {
  return arb_fpwrap_double_log_barnes_g(res, x, flags);
};

int arb_fpwrap_cdouble_log_barnes_g_(complex_double * res, complex_double * x, int flags) {
  return arb_fpwrap_cdouble_log_barnes_g(res, *x, flags);
};

int arb_fpwrap_double_polygamma_(double * res, double s, double z, int flags) {
  return arb_fpwrap_double_polygamma(res, s, z, flags);
};

int arb_fpwrap_cdouble_polygamma_(complex_double * res, complex_double * s, complex_double * z, int flags) {
  return arb_fpwrap_cdouble_polygamma(res, *s, *z, flags);
};

int arb_fpwrap_double_polylog_(double * res, double s, double z, int flags) {
  return arb_fpwrap_double_polylog(res, s, z, flags);
};

int arb_fpwrap_cdouble_polylog_(complex_double * res, complex_double * s, complex_double * z, int flags) {
  return arb_fpwrap_cdouble_polylog(res, *s, *z, flags);
};

int arb_fpwrap_cdouble_dirichlet_eta_(complex_double * res, complex_double * s, int flags) {
  return arb_fpwrap_cdouble_dirichlet_eta(res, *s, flags);
};

int arb_fpwrap_cdouble_riemann_xi_(complex_double * res, complex_double * s, int flags) {
  return arb_fpwrap_cdouble_riemann_xi(res, *s, flags);
};

int arb_fpwrap_cdouble_hardy_theta_(complex_double * res, complex_double * z, int flags) {
  return arb_fpwrap_cdouble_hardy_theta(res, *z, flags);
};

int arb_fpwrap_cdouble_hardy_z_(complex_double * res, complex_double * z, int flags) {
  return arb_fpwrap_cdouble_hardy_z(res, *z, flags);
};

int arb_fpwrap_cdouble_zeta_zero_(complex_double * res, ulong n, int flags) {
  return arb_fpwrap_cdouble_zeta_zero(res, n, flags);
};

int arb_fpwrap_double_erf_(double * res, double x, int flags) {
  return arb_fpwrap_double_erf(res, x, flags);
};

int arb_fpwrap_cdouble_erf_(complex_double * res, complex_double * x, int flags) {
  return arb_fpwrap_cdouble_erf(res, *x, flags);
};

int arb_fpwrap_double_erfc_(double * res, double x, int flags) {
  return arb_fpwrap_double_erfc(res, x, flags);
};

int arb_fpwrap_cdouble_erfc_(complex_double * res, complex_double * x, int flags) {
  return arb_fpwrap_cdouble_erfc(res, *x, flags);
};

int arb_fpwrap_double_erfi_(double * res, double x, int flags) {
  return arb_fpwrap_double_erfi(res, x, flags);
};

int arb_fpwrap_cdouble_erfi_(complex_double * res, complex_double * x, int flags) {
  return arb_fpwrap_cdouble_erfi(res, *x, flags);
};

int arb_fpwrap_double_erfinv_(double * res, double x, int flags) {
  return arb_fpwrap_double_erfinv(res, x, flags);
};

int arb_fpwrap_double_erfcinv_(double * res, double x, int flags) {
  return arb_fpwrap_double_erfcinv(res, x, flags);
};

int arb_fpwrap_double_fresnel_s_(double * res, double x, int normalized, int flags) {
  return arb_fpwrap_double_fresnel_s(res, x, normalized, flags);
};

int arb_fpwrap_cdouble_fresnel_s_(complex_double * res, complex_double * x, int normalized, int flags) {
  return arb_fpwrap_cdouble_fresnel_s(res, *x, normalized, flags);
};

int arb_fpwrap_double_fresnel_c_(double * res, double x, int normalized, int flags) {
  return arb_fpwrap_double_fresnel_c(res, x, normalized, flags);
};

int arb_fpwrap_cdouble_fresnel_c_(complex_double * res, complex_double * x, int normalized, int flags) {
  return arb_fpwrap_cdouble_fresnel_c(res, *x, normalized, flags);
};

int arb_fpwrap_double_gamma_upper_(double * res, double s, double z, int regularized, int flags) {
  return arb_fpwrap_double_gamma_upper(res, s, z, regularized, flags);
};

int arb_fpwrap_cdouble_gamma_upper_(complex_double * res, complex_double * s, complex_double * z, int regularized, int flags) {
  return arb_fpwrap_cdouble_gamma_upper(res, *s, *z, regularized, flags);
};

int arb_fpwrap_double_gamma_lower_(double * res, double s, double z, int regularized, int flags) {
  return arb_fpwrap_double_gamma_lower(res, s, z, regularized, flags);
};

int arb_fpwrap_cdouble_gamma_lower_(complex_double * res, complex_double * s, complex_double * z, int regularized, int flags) {
  return arb_fpwrap_cdouble_gamma_lower(res, *s, *z, regularized, flags);
};

int arb_fpwrap_double_beta_lower_(double * res, double a, double b, double z, int regularized, int flags) {
  return arb_fpwrap_double_beta_lower(res, a, b, z, regularized, flags);
};

int arb_fpwrap_cdouble_beta_lower_(complex_double * res, complex_double * a, complex_double * b, complex_double * z, int regularized, int flags) {
  return arb_fpwrap_cdouble_beta_lower(res, *a, *b, *z, regularized, flags);
};

int arb_fpwrap_double_exp_integral_e_(double * res, double s, double z, int flags) {
  return arb_fpwrap_double_exp_integral_e(res, s, z, flags);
};

int arb_fpwrap_cdouble_exp_integral_e_(complex_double * res, complex_double * s, complex_double * z, int flags) {
  return arb_fpwrap_cdouble_exp_integral_e(res, *s, *z, flags);
};

int arb_fpwrap_double_exp_integral_ei_(double * res, double x, int flags) {
  return arb_fpwrap_double_exp_integral_ei(res, x, flags);
};

int arb_fpwrap_cdouble_exp_integral_ei_(complex_double * res, complex_double * x, int flags) {
  return arb_fpwrap_cdouble_exp_integral_ei(res, *x, flags);
};

int arb_fpwrap_double_sin_integral_(double * res, double x, int flags) {
  return arb_fpwrap_double_sin_integral(res, x, flags);
};

int arb_fpwrap_cdouble_sin_integral_(complex_double * res, complex_double * x, int flags) {
  return arb_fpwrap_cdouble_sin_integral(res, *x, flags);
};

int arb_fpwrap_double_cos_integral_(double * res, double x, int flags) {
  return arb_fpwrap_double_cos_integral(res, x, flags);
};

int arb_fpwrap_cdouble_cos_integral_(complex_double * res, complex_double * x, int flags) {
  return arb_fpwrap_cdouble_cos_integral(res, *x, flags);
};

int arb_fpwrap_double_sinh_integral_(double * res, double x, int flags) {
  return arb_fpwrap_double_sinh_integral(res, x, flags);
};

int arb_fpwrap_cdouble_sinh_integral_(complex_double * res, complex_double * x, int flags) {
  return arb_fpwrap_cdouble_sinh_integral(res, *x, flags);
};

int arb_fpwrap_double_cosh_integral_(double * res, double x, int flags) {
  return arb_fpwrap_double_cosh_integral(res, x, flags);
};

int arb_fpwrap_cdouble_cosh_integral_(complex_double * res, complex_double * x, int flags) {
  return arb_fpwrap_cdouble_cosh_integral(res, *x, flags);
};

int arb_fpwrap_double_log_integral_(double * res, double x, int offset, int flags) {
  return arb_fpwrap_double_log_integral(res, x, offset, flags);
};

int arb_fpwrap_cdouble_log_integral_(complex_double * res, complex_double * x, int offset, int flags) {
  return arb_fpwrap_cdouble_log_integral(res, *x, offset, flags);
};

int arb_fpwrap_double_dilog_(double * res, double x, int flags) {
  return arb_fpwrap_double_dilog(res, x, flags);
};

int arb_fpwrap_cdouble_dilog_(complex_double * res, complex_double * x, int flags) {
  return arb_fpwrap_cdouble_dilog(res, *x, flags);
};

int arb_fpwrap_double_bessel_j_(double * res, double nu, double x, int flags) {
  return arb_fpwrap_double_bessel_j(res, nu, x, flags);
};

int arb_fpwrap_cdouble_bessel_j_(complex_double * res, complex_double * nu, complex_double * x, int flags) {
  return arb_fpwrap_cdouble_bessel_j(res, *nu, *x, flags);
};

int arb_fpwrap_double_bessel_y_(double * res, double nu, double x, int flags) {
  return arb_fpwrap_double_bessel_y(res, nu, x, flags);
};

int arb_fpwrap_cdouble_bessel_y_(complex_double * res, complex_double * nu, complex_double * x, int flags) {
  return arb_fpwrap_cdouble_bessel_y(res, *nu, *x, flags);
};

int arb_fpwrap_double_bessel_i_(double * res, double nu, double x, int flags) {
  return arb_fpwrap_double_bessel_i(res, nu, x, flags);
};

int arb_fpwrap_cdouble_bessel_i_(complex_double * res, complex_double * nu, complex_double * x, int flags) {
  return arb_fpwrap_cdouble_bessel_i(res, *nu, *x, flags);
};

int arb_fpwrap_double_bessel_k_(double * res, double nu, double x, int flags) {
  return arb_fpwrap_double_bessel_k(res, nu, x, flags);
};

int arb_fpwrap_cdouble_bessel_k_(complex_double * res, complex_double * nu, complex_double * x, int flags) {
  return arb_fpwrap_cdouble_bessel_k(res, *nu, *x, flags);
};

int arb_fpwrap_double_bessel_k_scaled_(double * res, double nu, double x, int flags) {
  return arb_fpwrap_double_bessel_k_scaled(res, nu, x, flags);
};

int arb_fpwrap_cdouble_bessel_k_scaled_(complex_double * res, complex_double * nu, complex_double * x, int flags) {
  return arb_fpwrap_cdouble_bessel_k_scaled(res, *nu, *x, flags);
};

int arb_fpwrap_double_airy_ai_(double * res, double x, int flags) {
  return arb_fpwrap_double_airy_ai(res, x, flags);
};

int arb_fpwrap_cdouble_airy_ai_(complex_double * res, complex_double * x, int flags) {
  return arb_fpwrap_cdouble_airy_ai(res, *x, flags);
};

int arb_fpwrap_double_airy_ai_prime_(double * res, double x, int flags) {
  return arb_fpwrap_double_airy_ai_prime(res, x, flags);
};

int arb_fpwrap_cdouble_airy_ai_prime_(complex_double * res, complex_double * x, int flags) {
  return arb_fpwrap_cdouble_airy_ai_prime(res, *x, flags);
};

int arb_fpwrap_double_airy_bi_(double * res, double x, int flags) {
  return arb_fpwrap_double_airy_bi(res, x, flags);
};

int arb_fpwrap_cdouble_airy_bi_(complex_double * res, complex_double * x, int flags) {
  return arb_fpwrap_cdouble_airy_bi(res, *x, flags);
};

int arb_fpwrap_double_airy_bi_prime_(double * res, double x, int flags) {
  return arb_fpwrap_double_airy_bi_prime(res, x, flags);
};

int arb_fpwrap_cdouble_airy_bi_prime_(complex_double * res, complex_double * x, int flags) {
  return arb_fpwrap_cdouble_airy_bi_prime(res, *x, flags);
};

int arb_fpwrap_double_airy_ai_zero_(double * res, ulong n, int flags) {
  return arb_fpwrap_double_airy_ai_zero(res, n, flags);
};

int arb_fpwrap_double_airy_ai_prime_zero_(double * res, ulong n, int flags) {
  return arb_fpwrap_double_airy_ai_prime_zero(res, n, flags);
};

int arb_fpwrap_double_airy_bi_zero_(double * res, ulong n, int flags) {
  return arb_fpwrap_double_airy_bi_zero(res, n, flags);
};

int arb_fpwrap_double_airy_bi_prime_zero_(double * res, ulong n, int flags) {
  return arb_fpwrap_double_airy_bi_prime_zero(res, n, flags);
};

int arb_fpwrap_double_coulomb_f_(double * res, double l, double eta, double x, int flags) {
  return arb_fpwrap_double_coulomb_f(res, l, eta, x, flags);
};

int arb_fpwrap_cdouble_coulomb_f_(complex_double * res, complex_double * l, complex_double * eta, complex_double * x, int flags) {
  return arb_fpwrap_cdouble_coulomb_f(res, *l, *eta, *x, flags);
};

int arb_fpwrap_double_coulomb_g_(double * res, double l, double eta, double x, int flags) {
  return arb_fpwrap_double_coulomb_g(res, l, eta, x, flags);
};

int arb_fpwrap_cdouble_coulomb_g_(complex_double * res, complex_double * l, complex_double * eta, complex_double * x, int flags) {
  return arb_fpwrap_cdouble_coulomb_g(res, *l, *eta, *x, flags);
};

int arb_fpwrap_cdouble_coulomb_hpos_(complex_double * res, complex_double * l, complex_double * eta, complex_double * x, int flags) {
  return arb_fpwrap_cdouble_coulomb_hpos(res, *l, *eta, *x, flags);
};

int arb_fpwrap_cdouble_coulomb_hneg_(complex_double * res, complex_double * l, complex_double * eta, complex_double * x, int flags) {
  return arb_fpwrap_cdouble_coulomb_hneg(res, *l, *eta, *x, flags);
};

int arb_fpwrap_double_chebyshev_t_(double * res, double n, double x, int flags) {
  return arb_fpwrap_double_chebyshev_t(res, n, x, flags);
};

int arb_fpwrap_cdouble_chebyshev_t_(complex_double * res, complex_double * n, complex_double * x, int flags) {
  return arb_fpwrap_cdouble_chebyshev_t(res, *n, *x, flags);
};

int arb_fpwrap_double_chebyshev_u_(double * res, double n, double x, int flags) {
  return arb_fpwrap_double_chebyshev_u(res, n, x, flags);
};

int arb_fpwrap_cdouble_chebyshev_u_(complex_double * res, complex_double * n, complex_double * x, int flags) {
  return arb_fpwrap_cdouble_chebyshev_u(res, *n, *x, flags);
};

int arb_fpwrap_double_jacobi_p_(double * res, double n, double a, double b, double x, int flags) {
  return arb_fpwrap_double_jacobi_p(res, n, a, b, x, flags);
};

int arb_fpwrap_cdouble_jacobi_p_(complex_double * res, complex_double * n, complex_double * a, complex_double * b, complex_double * x, int flags) {
  return arb_fpwrap_cdouble_jacobi_p(res, *n, *a, *b, *x, flags);
};

int arb_fpwrap_double_gegenbauer_c_(double * res, double n, double m, double x, int flags) {
  return arb_fpwrap_double_gegenbauer_c(res, n, m, x, flags);
};

int arb_fpwrap_cdouble_gegenbauer_c_(complex_double * res, complex_double * n, complex_double * m, complex_double * x, int flags) {
  return arb_fpwrap_cdouble_gegenbauer_c(res, *n, *m, *x, flags);
};

int arb_fpwrap_double_laguerre_l_(double * res, double n, double m, double x, int flags) {
  return arb_fpwrap_double_laguerre_l(res, n, m, x, flags);
};

int arb_fpwrap_cdouble_laguerre_l_(complex_double * res, complex_double * n, complex_double * m, complex_double * x, int flags) {
  return arb_fpwrap_cdouble_laguerre_l(res, *n, *m, *x, flags);
};

int arb_fpwrap_double_hermite_h_(double * res, double n, double x, int flags) {
  return arb_fpwrap_double_hermite_h(res, n, x, flags);
};

int arb_fpwrap_cdouble_hermite_h_(complex_double * res, complex_double * n, complex_double * x, int flags) {
  return arb_fpwrap_cdouble_hermite_h(res, *n, *x, flags);
};

int arb_fpwrap_double_legendre_p_(double * res, double n, double m, double x, int type, int flags) {
  return arb_fpwrap_double_legendre_p(res, n, m, x, type, flags);
};

int arb_fpwrap_cdouble_legendre_p_(complex_double * res, complex_double * n, complex_double * m, complex_double * x, int type, int flags) {
  return arb_fpwrap_cdouble_legendre_p(res, *n, *m, *x, type, flags);
};

int arb_fpwrap_double_legendre_q_(double * res, double n, double m, double x, int type, int flags) {
  return arb_fpwrap_double_legendre_q(res, n, m, x, type, flags);
};

int arb_fpwrap_cdouble_legendre_q_(complex_double * res, complex_double * n, complex_double * m, complex_double * x, int type, int flags) {
  return arb_fpwrap_cdouble_legendre_q(res, *n, *m, *x, type, flags);
};

int arb_fpwrap_double_legendre_root_(double * res1, double * res2, ulong n, ulong k, int flags) {
  return arb_fpwrap_double_legendre_root(res1, res2, n, k, flags);
};

int arb_fpwrap_cdouble_spherical_y_(complex_double * res, slong n, slong m, complex_double * x1, complex_double * x2, int flags) {
  return arb_fpwrap_cdouble_spherical_y(res, n, m, *x1, *x2, flags);
};

int arb_fpwrap_double_hypgeom_0f1_(double * res, double a, double x, int regularized, int flags) {
  return arb_fpwrap_double_hypgeom_0f1(res, a, x, regularized, flags);
};

int arb_fpwrap_cdouble_hypgeom_0f1_(complex_double * res, complex_double * a, complex_double * x, int regularized, int flags) {
  return arb_fpwrap_cdouble_hypgeom_0f1(res, *a, *x, regularized, flags);
};

int arb_fpwrap_double_hypgeom_1f1_(double * res, double a, double b, double x, int regularized, int flags) {
  return arb_fpwrap_double_hypgeom_1f1(res, a, b, x, regularized, flags);
};

int arb_fpwrap_cdouble_hypgeom_1f1_(complex_double * res, complex_double * a, complex_double * b, complex_double * x, int regularized, int flags) {
  return arb_fpwrap_cdouble_hypgeom_1f1(res, *a, *b, *x, regularized, flags);
};

int arb_fpwrap_double_hypgeom_u_(double * res, double a, double b, double x, int flags) {
  return arb_fpwrap_double_hypgeom_u(res, a, b, x, flags);
};

int arb_fpwrap_cdouble_hypgeom_u_(complex_double * res, complex_double * a, complex_double * b, complex_double * x, int flags) {
  return arb_fpwrap_cdouble_hypgeom_u(res, *a, *b, *x, flags);
};

int arb_fpwrap_double_hypgeom_2f1_(double * res, double a, double b, double c, double x, int regularized, int flags) {
  return arb_fpwrap_double_hypgeom_2f1(res, a, b, c, x, regularized, flags);
};

int arb_fpwrap_cdouble_hypgeom_2f1_(complex_double * res, complex_double * a, complex_double * b, complex_double * c, complex_double * x, int regularized, int flags) {
  return arb_fpwrap_cdouble_hypgeom_2f1(res, *a, *b, *c, *x, regularized, flags);
};

int arb_fpwrap_double_hypgeom_pfq_(double * res, const double * a, slong p, const double * b, slong q, double z, int regularized, int flags) {
  return arb_fpwrap_double_hypgeom_pfq(res, a, p, b, q, z, regularized, flags);
};

int arb_fpwrap_cdouble_hypgeom_pfq_(complex_double * res, const complex_double * a, slong p, const complex_double * b, slong q, complex_double * z, int regularized, int flags) {
  return arb_fpwrap_cdouble_hypgeom_pfq(res, a, p, b, q, *z, regularized, flags);
};

int arb_fpwrap_double_agm_(double * res, double x, double y, int flags) {
  return arb_fpwrap_double_agm(res, x, y, flags);
};

int arb_fpwrap_cdouble_agm_(complex_double * res, complex_double * x, complex_double * y, int flags) {
  return arb_fpwrap_cdouble_agm(res, *x, *y, flags);
};

int arb_fpwrap_cdouble_elliptic_k_(complex_double * res, complex_double * m, int flags) {
  return arb_fpwrap_cdouble_elliptic_k(res, *m, flags);
};

int arb_fpwrap_cdouble_elliptic_e_(complex_double * res, complex_double * m, int flags) {
  return arb_fpwrap_cdouble_elliptic_e(res, *m, flags);
};

int arb_fpwrap_cdouble_elliptic_pi_(complex_double * res, complex_double * n, complex_double * m, int flags) {
  return arb_fpwrap_cdouble_elliptic_pi(res, *n, *m, flags);
};

int arb_fpwrap_cdouble_elliptic_f_(complex_double * res, complex_double * phi, complex_double * m, int pi, int flags) {
  return arb_fpwrap_cdouble_elliptic_f(res, *phi, *m, pi, flags);
};

int arb_fpwrap_cdouble_elliptic_e_inc_(complex_double * res, complex_double * phi, complex_double * m, int pi, int flags) {
  return arb_fpwrap_cdouble_elliptic_e_inc(res, *phi, *m, pi, flags);
};

int arb_fpwrap_cdouble_elliptic_pi_inc_(complex_double * res, complex_double * n, complex_double * phi, complex_double * m, int pi, int flags) {
  return arb_fpwrap_cdouble_elliptic_pi_inc(res, *n, *phi, *m, pi, flags);
};

int arb_fpwrap_cdouble_elliptic_rf_(complex_double * res, complex_double * x, complex_double * y, complex_double * z, int option, int flags) {
  return arb_fpwrap_cdouble_elliptic_rf(res, *x, *y, *z, option, flags);
};

int arb_fpwrap_cdouble_elliptic_rg_(complex_double * res, complex_double * x, complex_double * y, complex_double * z, int option, int flags) {
  return arb_fpwrap_cdouble_elliptic_rg(res, *x, *y, *z, option, flags);
};

int arb_fpwrap_cdouble_elliptic_rj_(complex_double * res, complex_double * x, complex_double * y, complex_double * z, complex_double * w, int option, int flags) {
  return arb_fpwrap_cdouble_elliptic_rj(res, *x, *y, *z, *w, option, flags);
};

int arb_fpwrap_cdouble_elliptic_p_(complex_double * res, complex_double * z, complex_double * tau, int flags) {
  return arb_fpwrap_cdouble_elliptic_p(res, *z, *tau, flags);
};

int arb_fpwrap_cdouble_elliptic_p_prime_(complex_double * res, complex_double * z, complex_double * tau, int flags) {
  return arb_fpwrap_cdouble_elliptic_p_prime(res, *z, *tau, flags);
};

int arb_fpwrap_cdouble_elliptic_inv_p_(complex_double * res, complex_double * z, complex_double * tau, int flags) {
  return arb_fpwrap_cdouble_elliptic_inv_p(res, *z, *tau, flags);
};

int arb_fpwrap_cdouble_elliptic_zeta_(complex_double * res, complex_double * z, complex_double * tau, int flags) {
  return arb_fpwrap_cdouble_elliptic_zeta(res, *z, *tau, flags);
};

int arb_fpwrap_cdouble_elliptic_sigma_(complex_double * res, complex_double * z, complex_double * tau, int flags) {
  return arb_fpwrap_cdouble_elliptic_sigma(res, *z, *tau, flags);
};

int arb_fpwrap_cdouble_jacobi_theta_1_(complex_double * res, complex_double * z, complex_double * tau, int flags) {
  return arb_fpwrap_cdouble_jacobi_theta_1(res, *z, *tau, flags);
};

int arb_fpwrap_cdouble_jacobi_theta_2_(complex_double * res, complex_double * z, complex_double * tau, int flags) {
  return arb_fpwrap_cdouble_jacobi_theta_2(res, *z, *tau, flags);
};

int arb_fpwrap_cdouble_jacobi_theta_3_(complex_double * res, complex_double * z, complex_double * tau, int flags) {
  return arb_fpwrap_cdouble_jacobi_theta_3(res, *z, *tau, flags);
};

int arb_fpwrap_cdouble_jacobi_theta_4_(complex_double * res, complex_double * z, complex_double * tau, int flags) {
  return arb_fpwrap_cdouble_jacobi_theta_4(res, *z, *tau, flags);
};

int arb_fpwrap_cdouble_dedekind_eta_(complex_double * res, complex_double * tau, int flags) {
  return arb_fpwrap_cdouble_dedekind_eta(res, *tau, flags);
};

int arb_fpwrap_cdouble_modular_j_(complex_double * res, complex_double * tau, int flags) {
  return arb_fpwrap_cdouble_modular_j(res, *tau, flags);
};

int arb_fpwrap_cdouble_modular_lambda_(complex_double * res, complex_double * tau, int flags) {
  return arb_fpwrap_cdouble_modular_lambda(res, *tau, flags);
};

int arb_fpwrap_cdouble_modular_delta_(complex_double * res, complex_double * tau, int flags) {
  return arb_fpwrap_cdouble_modular_delta(res, *tau, flags);
};

