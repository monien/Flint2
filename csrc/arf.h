#ifndef ARF_H_
#define ARF_H_

#include <arf.h>
#include <mag.h>

int arf_rounds_down_(arf_rnd_t rnd, int sgnbit);
int arf_rounds_up_(arf_rnd_t rnd, int sgnbit);
mpfr_rnd_t arf_rnd_to_mpfr_(arf_rnd_t rnd);
void arf_init_(arf_t x);
void arf_zero_(arf_t x);
void arf_pos_inf_(arf_t x);
void arf_neg_inf_(arf_t x);
void arf_nan_(arf_t x);
int arf_is_special_(const arf_t x);
int arf_is_zero_(const arf_t x);
int arf_is_pos_inf_(const arf_t x);
int arf_is_neg_inf_(const arf_t x);
int arf_is_nan_(const arf_t x);
int arf_is_normal_(const arf_t x);
int arf_is_finite_(const arf_t x);
int arf_is_inf_(const arf_t x);
void arf_one_(arf_t x);
int arf_is_one_(const arf_t x);
int arf_sgn_(const arf_t x);
void arf_swap_(arf_t y, arf_t x);
void arf_neg_(arf_t y, const arf_t x);
void arf_init_set_ui_(arf_t x, ulong v);
void arf_init_set_si_(arf_t x, slong v);
void arf_set_ui_(arf_t x, ulong v);
void arf_set_si_(arf_t x, slong v);
void arf_init_set_shallow_(arf_t z, const arf_t x);
void arf_init_neg_shallow_(arf_t z, const arf_t x);
void arf_init_set_mag_shallow_(arf_t y, const mag_t x);
void arf_init_neg_mag_shallow_(arf_t z, const mag_t x);
int arf_cmpabs_mag_(const arf_t x, const mag_t y);
int arf_mag_cmpabs_(const mag_t x, const arf_t y);
void arf_set_mpz_(arf_t y, const mpz_t x);
void arf_set_fmpz_(arf_t y, const fmpz_t x);
int arf_set_round_ui_(arf_t x, ulong v, slong prec, arf_rnd_t rnd);
int arf_set_round_si_(arf_t x, slong v, slong prec, arf_rnd_t rnd);
int arf_set_round_mpz_(arf_t y, const mpz_t x, slong prec, arf_rnd_t rnd);
int arf_set_round_fmpz_(arf_t y, const fmpz_t x, slong prec, arf_rnd_t rnd);
void arf_min_(arf_t z, const arf_t a, const arf_t b);
void arf_max_(arf_t z, const arf_t a, const arf_t b);
void arf_abs_(arf_t y, const arf_t x);
slong arf_bits_(const arf_t x);
void arf_bot_(fmpz_t e, const arf_t x);
void arf_set_si_2exp_si_(arf_t x, slong man, slong exp);
void arf_mul_(arf_t z, arf_t x, arf_t y, slong prec, arf_rnd_t rnd);
void arf_set_ui_2exp_si_(arf_t x, ulong man, slong exp);
void arf_mul_2exp_si_(arf_t y, const arf_t x, slong e);
void arf_mul_2exp_fmpz_(arf_t y, const arf_t x, const fmpz_t e);
int arf_set_round_fmpz_2exp_(arf_t y, const fmpz_t x, const fmpz_t exp, slong prec, arf_rnd_t rnd);
void arf_abs_bound_lt_2exp_fmpz_(fmpz_t b, const arf_t x);
void arf_abs_bound_le_2exp_fmpz_(fmpz_t b, const arf_t x);
int arf_neg_mul_(arf_t z, const arf_t x, const arf_t y, slong prec, arf_rnd_t rnd);
int arf_mul_ui_(arf_ptr z, arf_srcptr x, ulong y, slong prec, arf_rnd_t rnd);
int arf_mul_si_(arf_ptr z, arf_srcptr x, slong y, slong prec, arf_rnd_t rnd);
int arf_mul_fmpz_(arf_ptr z, arf_srcptr x, const fmpz_t y, slong prec, arf_rnd_t rnd);
int arf_addmul_ui_(arf_ptr z, arf_srcptr x, ulong y, slong prec, arf_rnd_t rnd);
int arf_addmul_si_(arf_ptr z, arf_srcptr x, slong y, slong prec, arf_rnd_t rnd);
int arf_addmul_fmpz_(arf_ptr z, arf_srcptr x, const fmpz_t y, slong prec, arf_rnd_t rnd);
int arf_submul_ui_(arf_ptr z, arf_srcptr x, ulong y, slong prec, arf_rnd_t rnd);
int arf_submul_si_(arf_ptr z, arf_srcptr x, slong y, slong prec, arf_rnd_t rnd);
int arf_submul_fmpz_(arf_ptr z, arf_srcptr x, const fmpz_t y, slong prec, arf_rnd_t rnd);
int arf_div_ui_(arf_ptr z, arf_srcptr x, ulong y, slong prec, arf_rnd_t rnd);
int arf_ui_div_(arf_ptr z, ulong x, arf_srcptr y, slong prec, arf_rnd_t rnd);
int arf_div_si_(arf_ptr z, arf_srcptr x, slong y, slong prec, arf_rnd_t rnd);
int arf_si_div_(arf_ptr z, slong x, arf_srcptr y, slong prec, arf_rnd_t rnd);
int arf_div_fmpz_(arf_ptr z, arf_srcptr x, const fmpz_t y, slong prec, arf_rnd_t rnd);
int arf_fmpz_div_(arf_ptr z, const fmpz_t x, arf_srcptr y, slong prec, arf_rnd_t rnd);
int arf_fmpz_div_fmpz_(arf_ptr z, const fmpz_t x, const fmpz_t y, slong prec, arf_rnd_t rnd);
void arf_set_mag_(arf_t y, const mag_t x);
void arf_mag_fast_add_ulp_(mag_t z, const mag_t x, const arf_t y, slong prec);
void arf_mag_add_ulp_(mag_t z, const mag_t x, const arf_t y, slong prec);
void arf_mag_set_ulp_(mag_t z, const arf_t y, slong prec);
int arf_set_fmpq_(arf_t y, const fmpq_t x, slong prec, arf_rnd_t rnd);
slong arf_allocated_bytes_(const arf_t x);

#endif // ARF_H_
