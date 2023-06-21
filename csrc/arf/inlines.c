
int
arf_rounds_down_(arf_rnd_t rnd, int sgnbit)
{
    if (rnd == ARF_RND_DOWN) return 1;
    if (rnd == ARF_RND_UP) return 0;
    if (rnd == ARF_RND_FLOOR) return !sgnbit;
    return sgnbit;
}

int
arf_rounds_up_(arf_rnd_t rnd, int sgnbit)
{
    if (rnd == ARF_RND_DOWN) return 0;
    if (rnd == ARF_RND_UP) return 1;
    if (rnd == ARF_RND_FLOOR) return sgnbit;
    return !sgnbit;
}

mpfr_rnd_t
arf_rnd_to_mpfr_(arf_rnd_t rnd)
{
    if (rnd == ARF_RND_DOWN) return MPFR_RNDZ;
    else if (rnd == ARF_RND_UP) return MPFR_RNDA;
    else if (rnd == ARF_RND_FLOOR) return MPFR_RNDD;
    else if (rnd == ARF_RND_CEIL) return MPFR_RNDU;
    else return MPFR_RNDN;
}

void
arf_init_(arf_t x)
{
    fmpz_init(ARF_EXPREF(x));
    ARF_XSIZE(x) = 0;
}

void
arf_zero_(arf_t x)
{
    ARF_MAKE_SPECIAL(x);
    ARF_EXP(x) = ARF_EXP_ZERO;
}

void
arf_pos_inf_(arf_t x)
{
    ARF_MAKE_SPECIAL(x);
    ARF_EXP(x) = ARF_EXP_POS_INF;
}

void
arf_neg_inf_(arf_t x)
{
    ARF_MAKE_SPECIAL(x);
    ARF_EXP(x) = ARF_EXP_NEG_INF;
}

void
arf_nan_(arf_t x)
{
    ARF_MAKE_SPECIAL(x);
    ARF_EXP(x) = ARF_EXP_NAN;
}

int
arf_is_special_(const arf_t x)
{
    return ARF_IS_SPECIAL(x);
}

int
arf_is_zero_(const arf_t x)
{
    return ARF_IS_SPECIAL(x) && (ARF_EXP(x) == ARF_EXP_ZERO);
}

int
arf_is_pos_inf_(const arf_t x)
{
    return ARF_IS_SPECIAL(x) && (ARF_EXP(x) == ARF_EXP_POS_INF);
}

int
arf_is_neg_inf_(const arf_t x)
{
    return ARF_IS_SPECIAL(x) && (ARF_EXP(x) == ARF_EXP_NEG_INF);
}

int
arf_is_nan_(const arf_t x)
{
    return ARF_IS_SPECIAL(x) && (ARF_EXP(x) == ARF_EXP_NAN);
}

int
arf_is_normal_(const arf_t x)
{
    return !ARF_IS_SPECIAL(x);
}

int
arf_is_finite_(const arf_t x)
{
    return !ARF_IS_SPECIAL(x) || (ARF_EXP(x) == ARF_EXP_ZERO);
}

int
arf_is_inf_(const arf_t x)
{
    return ARF_IS_SPECIAL(x) && (ARF_EXP(x) == ARF_EXP_POS_INF ||
                                 ARF_EXP(x) == ARF_EXP_NEG_INF);
}

void
arf_one_(arf_t x)
{
    fmpz_clear(ARF_EXPREF(x));
    ARF_DEMOTE(x);
    ARF_EXP(x) = 1;
    ARF_XSIZE(x) = ARF_MAKE_XSIZE(1, 0);
    ARF_NOPTR_D(x)[0] = LIMB_TOP;
}

int
arf_is_one_(const arf_t x)
{
    return (ARF_EXP(x) == 1) && (ARF_XSIZE(x) == ARF_MAKE_XSIZE(1, 0))
                             && ARF_NOPTR_D(x)[0] == LIMB_TOP;
}

int
arf_sgn_(const arf_t x)
{
    if (arf_is_special(x))
    {
        if (arf_is_zero(x) || arf_is_nan(x))
            return 0;
        return arf_is_pos_inf(x) ? 1 : -1;
    }
    else
    {
        return ARF_SGNBIT(x) ? -1 : 1;
    }
}

void
arf_swap_(arf_t y, arf_t x)
{
    if (x != y)
    {
        arf_struct t = *x;
        *x = *y;
        *y = t;
    }
}

void
arf_neg_(arf_t y, const arf_t x)
{
    arf_set(y, x);

    if (arf_is_special(y))
    {
        if (arf_is_pos_inf(y))
            arf_neg_inf(y);
        else if (arf_is_neg_inf(y))
            arf_pos_inf(y);
    }
    else
    {
        ARF_NEG(y);
    }
}

void
arf_init_set_ui_(arf_t x, ulong v)
{
    if (v == 0)
    {
        ARF_EXP(x) = ARF_EXP_ZERO;
        ARF_XSIZE(x) = 0;
    }
    else
    {
        unsigned int c;
        c = flint_clz(v);
        ARF_EXP(x) = FLINT_BITS - c;
        ARF_NOPTR_D(x)[0] = v << c;
        ARF_XSIZE(x) = ARF_MAKE_XSIZE(1, 0);
    }
}

/* FLINT_ABS is unsafe for x = WORD_MIN */
#define UI_ABS_SI(x) (((slong)(x) < 0) ? (-(ulong)(x)) : ((ulong)(x)))

void
arf_init_set_si_(arf_t x, slong v)
{
    arf_init_set_ui(x, UI_ABS_SI(v));
    if (v < 0)
        ARF_NEG(x);
}

void
arf_set_ui_(arf_t x, ulong v)
{
    ARF_DEMOTE(x);
    _fmpz_demote(ARF_EXPREF(x));

    if (v == 0)
    {
        ARF_EXP(x) = ARF_EXP_ZERO;
        ARF_XSIZE(x) = 0;
    }
    else
    {
        unsigned int c;
        c = flint_clz(v);
        ARF_EXP(x) = FLINT_BITS - c;
        ARF_NOPTR_D(x)[0] = v << c;
        ARF_XSIZE(x) = ARF_MAKE_XSIZE(1, 0);
    }
}

void
arf_set_si_(arf_t x, slong v)
{
    arf_set_ui(x, UI_ABS_SI(v));
    if (v < 0)
        ARF_NEG(x);
}

void
arf_init_set_shallow_(arf_t z, const arf_t x)
{
    *z = *x;
}

void
arf_init_neg_shallow_(arf_t z, const arf_t x)
{
    *z = *x;
    arf_neg(z, z);
}

void
arf_init_set_mag_shallow_(arf_t y, const mag_t x)
{
    mp_limb_t t = MAG_MAN(x);
    ARF_XSIZE(y) = ARF_MAKE_XSIZE(t != 0, 0);
    ARF_EXP(y) = MAG_EXP(x);
    ARF_NOPTR_D(y)[0] = t << (FLINT_BITS - MAG_BITS);
}

void
arf_init_neg_mag_shallow_(arf_t z, const mag_t x)
{
    arf_init_set_mag_shallow(z, x);
    arf_neg(z, z);
}

int
arf_cmpabs_mag_(const arf_t x, const mag_t y)
{
    arf_t t;
    arf_init_set_mag_shallow(t, y);  /* no need to free */
    return arf_cmpabs(x, t);
}

int
arf_mag_cmpabs_(const mag_t x, const arf_t y)
{
    arf_t t;
    arf_init_set_mag_shallow(t, x);  /* no need to free */
    return arf_cmpabs(t, y);
}

void
arf_set_mpz_(arf_t y, const mpz_t x)
{
    slong size = x->_mp_size;

    if (size == 0)
        arf_zero(y);
    else
        arf_set_mpn(y, x->_mp_d, FLINT_ABS(size), size < 0);
}

void
arf_set_fmpz_(arf_t y, const fmpz_t x)
{
    if (!COEFF_IS_MPZ(*x))
        arf_set_si(y, *x);
    else
        arf_set_mpz(y, COEFF_TO_PTR(*x));
}

int
arf_set_round_ui_(arf_t x, ulong v, slong prec, arf_rnd_t rnd)
{
    return _arf_set_round_ui(x, v, 0, prec, rnd);
}

int
arf_set_round_si_(arf_t x, slong v, slong prec, arf_rnd_t rnd)
{
    return _arf_set_round_ui(x, UI_ABS_SI(v), v < 0, prec, rnd);
}

int
arf_set_round_mpz_(arf_t y, const mpz_t x, slong prec, arf_rnd_t rnd)
{
    int inexact;
    slong size = x->_mp_size;
    slong fix;

    if (size == 0)
    {
        arf_zero(y);
        return 0;
    }

    inexact = _arf_set_round_mpn(y, &fix, x->_mp_d, FLINT_ABS(size),
        (size < 0), prec, rnd);
    _fmpz_demote(ARF_EXPREF(y));
    ARF_EXP(y) = FLINT_ABS(size) * FLINT_BITS + fix;
    return inexact;
}

int
arf_set_round_fmpz_(arf_t y, const fmpz_t x, slong prec, arf_rnd_t rnd)
{
    if (!COEFF_IS_MPZ(*x))
        return arf_set_round_si(y, *x, prec, rnd);
    else
        return arf_set_round_mpz(y, COEFF_TO_PTR(*x), prec, rnd);
}

void
arf_min_(arf_t z, const arf_t a, const arf_t b)
{
    if (arf_cmp(a, b) <= 0)
        arf_set(z, a);
    else
        arf_set(z, b);
}

void
arf_max_(arf_t z, const arf_t a, const arf_t b)
{
    if (arf_cmp(a, b) > 0)
        arf_set(z, a);
    else
        arf_set(z, b);
}

void
arf_abs_(arf_t y, const arf_t x)
{
    if (arf_sgn(x) < 0)
        arf_neg(y, x);
    else
        arf_set(y, x);
}

slong
arf_bits_(const arf_t x)
{
    if (arf_is_special(x))
        return 0;
    else
    {
        mp_srcptr xp;
        mp_size_t xn;
        slong c;

        ARF_GET_MPN_READONLY(xp, xn, x);
        c = flint_ctz(xp[0]);
        return xn * FLINT_BITS - c;
    }
}

void
arf_bot_(fmpz_t e, const arf_t x)
{
    if (arf_is_special(x))
        fmpz_zero(e);
    else
        fmpz_sub_si(e, ARF_EXPREF(x), arf_bits(x));
}

void
arf_set_si_2exp_si_(arf_t x, slong man, slong exp)
{
    arf_set_si(x, man);
    if (man != 0)
        fmpz_add_si_inline(ARF_EXPREF(x), ARF_EXPREF(x), exp);
}

void
arf_set_ui_2exp_si_(arf_t x, ulong man, slong exp)
{
    arf_set_ui(x, man);
    if (man != 0)
        fmpz_add_si_inline(ARF_EXPREF(x), ARF_EXPREF(x), exp);
}

void
arf_mul_2exp_si_(arf_t y, const arf_t x, slong e)
{
    arf_set(y, x);
    if (!arf_is_special(y))
        fmpz_add_si_inline(ARF_EXPREF(y), ARF_EXPREF(y), e);
}

void
arf_mul_2exp_fmpz_(arf_t y, const arf_t x, const fmpz_t e)
{
    arf_set(y, x);
    if (!arf_is_special(y))
        fmpz_add_inline(ARF_EXPREF(y), ARF_EXPREF(y), e);
}

int
arf_set_round_fmpz_2exp_(arf_t y, const fmpz_t x, const fmpz_t exp, slong prec, arf_rnd_t rnd)
{
    if (fmpz_is_zero(x))
    {
        arf_zero(y);
        return 0;
    }
    else
    {
        int r = arf_set_round_fmpz(y, x, prec, rnd);
        fmpz_add_inline(ARF_EXPREF(y), ARF_EXPREF(y), exp);
        return r;
    }
}

void
arf_abs_bound_lt_2exp_fmpz_(fmpz_t b, const arf_t x)
{
    if (arf_is_special(x))
        fmpz_zero(b);
    else
        fmpz_set(b, ARF_EXPREF(x));
}

void
arf_abs_bound_le_2exp_fmpz_(fmpz_t b, const arf_t x)
{
    if (arf_is_special(x))
        fmpz_zero(b);
    else if (ARF_IS_POW2(x))
        fmpz_sub_ui(b, ARF_EXPREF(x), 1);
    else
        fmpz_set(b, ARF_EXPREF(x));
}

int
arf_neg_mul_(arf_t z, const arf_t x, const arf_t y, slong prec, arf_rnd_t rnd)
{
    if (arf_is_special(y))
    {
        arf_mul(z, x, y, prec, rnd);
        arf_neg(z, z);
        return 0;
    }
    else
    {
        arf_t t;
        *t = *y;
        ARF_NEG(t);
        return arf_mul(z, x, t, prec, rnd);
    }
}

int
arf_mul_ui_(arf_ptr z, arf_srcptr x, ulong y, slong prec, arf_rnd_t rnd)
{
    arf_t t;
    arf_init_set_ui(t, y); /* no need to free */
    return arf_mul(z, x, t, prec, rnd);
}

int
arf_mul_si_(arf_ptr z, arf_srcptr x, slong y, slong prec, arf_rnd_t rnd)
{
    arf_t t;
    arf_init_set_si(t, y); /* no need to free */
    return arf_mul(z, x, t, prec, rnd);
}

int
arf_mul_fmpz_(arf_ptr z, arf_srcptr x, const fmpz_t y, slong prec, arf_rnd_t rnd)
{
    if (!COEFF_IS_MPZ(*y))
        return arf_mul_si(z, x, *y, prec, rnd);
    else
        return arf_mul_mpz(z, x, COEFF_TO_PTR(*y), prec, rnd);
}

int
arf_addmul_ui_(arf_ptr z, arf_srcptr x, ulong y, slong prec, arf_rnd_t rnd)
{
    arf_t t;
    arf_init_set_ui(t, y); /* no need to free */
    return arf_addmul(z, x, t, prec, rnd);
}

int
arf_addmul_si_(arf_ptr z, arf_srcptr x, slong y, slong prec, arf_rnd_t rnd)
{
    arf_t t;
    arf_init_set_si(t, y); /* no need to free */
    return arf_addmul(z, x, t, prec, rnd);
}

int
arf_addmul_fmpz_(arf_ptr z, arf_srcptr x, const fmpz_t y, slong prec, arf_rnd_t rnd)
{
    if (!COEFF_IS_MPZ(*y))
        return arf_addmul_si(z, x, *y, prec, rnd);
    else
        return arf_addmul_mpz(z, x, COEFF_TO_PTR(*y), prec, rnd);
}

int
arf_submul_ui_(arf_ptr z, arf_srcptr x, ulong y, slong prec, arf_rnd_t rnd)
{
    arf_t t;
    arf_init_set_ui(t, y); /* no need to free */
    return arf_submul(z, x, t, prec, rnd);
}

int
arf_submul_si_(arf_ptr z, arf_srcptr x, slong y, slong prec, arf_rnd_t rnd)
{
    arf_t t;
    arf_init_set_si(t, y); /* no need to free */
    return arf_submul(z, x, t, prec, rnd);
}

int
arf_submul_fmpz_(arf_ptr z, arf_srcptr x, const fmpz_t y, slong prec, arf_rnd_t rnd)
{
    if (!COEFF_IS_MPZ(*y))
        return arf_submul_si(z, x, *y, prec, rnd);
    else
        return arf_submul_mpz(z, x, COEFF_TO_PTR(*y), prec, rnd);
}

int
arf_div_ui_(arf_ptr z, arf_srcptr x, ulong y, slong prec, arf_rnd_t rnd)
{
    arf_t t;
    arf_init_set_ui(t, y); /* no need to free */
    return arf_div(z, x, t, prec, rnd);
}

int
arf_ui_div_(arf_ptr z, ulong x, arf_srcptr y, slong prec, arf_rnd_t rnd)
{
    arf_t t;
    arf_init_set_ui(t, x); /* no need to free */
    return arf_div(z, t, y, prec, rnd);
}

int
arf_div_si_(arf_ptr z, arf_srcptr x, slong y, slong prec, arf_rnd_t rnd)
{
    arf_t t;
    arf_init_set_si(t, y); /* no need to free */
    return arf_div(z, x, t, prec, rnd);
}

int
arf_si_div_(arf_ptr z, slong x, arf_srcptr y, slong prec, arf_rnd_t rnd)
{
    arf_t t;
    arf_init_set_si(t, x); /* no need to free */
    return arf_div(z, t, y, prec, rnd);
}

int
arf_div_fmpz_(arf_ptr z, arf_srcptr x, const fmpz_t y, slong prec, arf_rnd_t rnd)
{
    arf_t t;
    int r;
    arf_init(t);
    arf_set_fmpz(t, y);
    r = arf_div(z, x, t, prec, rnd);
    arf_clear(t);
    return r;
}

int
arf_fmpz_div_(arf_ptr z, const fmpz_t x, arf_srcptr y, slong prec, arf_rnd_t rnd)
{
    arf_t t;
    int r;
    arf_init(t);
    arf_set_fmpz(t, x);
    r = arf_div(z, t, y, prec, rnd);
    arf_clear(t);
    return r;
}

int
arf_fmpz_div_fmpz_(arf_ptr z, const fmpz_t x, const fmpz_t y, slong prec, arf_rnd_t rnd)
{
    arf_t t, u;
    int r;
    arf_init(t);
    arf_init(u);
    arf_set_fmpz(t, x);
    arf_set_fmpz(u, y);
    r = arf_div(z, t, u, prec, rnd);
    arf_clear(t);
    arf_clear(u);
    return r;
}

void
arf_set_mag_(arf_t y, const mag_t x)
{
    if (mag_is_zero(x))
    {
        arf_zero(y);
    }
    else if (mag_is_inf(x))
    {
        arf_pos_inf(y);
    }
    else
    {
        _fmpz_set_fast(ARF_EXPREF(y), MAG_EXPREF(x));
        ARF_DEMOTE(y);
        ARF_XSIZE(y) = ARF_MAKE_XSIZE(1, 0);
        ARF_NOPTR_D(y)[0] = MAG_MAN(x) << (FLINT_BITS - MAG_BITS);
    }
}

void
mag_init_set_arf(mag_t y, const arf_t x)
{
    mag_init(y);
    arf_get_mag(y, x);
}

void
mag_fast_init_set_arf(mag_t y, const arf_t x)
{
    if (ARF_IS_SPECIAL(x))   /* x == 0 */
    {
        mag_fast_zero(y);
    }
    else
    {
        mp_srcptr xp;
        mp_size_t xn;

        ARF_GET_MPN_READONLY(xp, xn, x);

        MAG_MAN(y) = (xp[xn - 1] >> (FLINT_BITS - MAG_BITS)) + LIMB_ONE;
        MAG_EXP(y) = ARF_EXP(x);

        MAG_FAST_ADJUST_ONE_TOO_LARGE(y);
    }
}

void
arf_mag_fast_add_ulp_(mag_t z, const mag_t x, const arf_t y, slong prec)
{
    mag_fast_add_2exp_si(z, x, ARF_EXP(y) - prec);
}

void
arf_mag_add_ulp_(mag_t z, const mag_t x, const arf_t y, slong prec)
{
    if (ARF_IS_SPECIAL(y))
    {
        flint_printf("error: ulp error not defined for special value!\n");
        flint_abort();
    }
    else if (MAG_IS_LAGOM(z) && MAG_IS_LAGOM(x) && ARF_IS_LAGOM(y))
    {
        arf_mag_fast_add_ulp(z, x, y, prec);
    }
    else
    {
        fmpz_t e;
        fmpz_init(e);
        fmpz_sub_ui(e, ARF_EXPREF(y), prec);
        mag_add_2exp_fmpz(z, x, e);
        fmpz_clear(e);
    }
}

void
arf_mag_set_ulp_(mag_t z, const arf_t y, slong prec)
{
    if (ARF_IS_SPECIAL(y))
    {
        flint_printf("error: ulp error not defined for special value!\n");
        flint_abort();
    }
    else
    {
        _fmpz_add_fast(MAG_EXPREF(z), ARF_EXPREF(y), 1 - prec);
        MAG_MAN(z) = MAG_ONE_HALF;
    }
}

int
arf_set_fmpq_(arf_t y, const fmpq_t x, slong prec, arf_rnd_t rnd)
{
    return arf_fmpz_div_fmpz(y, fmpq_numref(x), fmpq_denref(x), prec, rnd);
}

slong
arf_allocated_bytes_(const arf_t x)
{
    slong size = fmpz_allocated_bytes(ARF_EXPREF(x));

    if (ARF_HAS_PTR(x))
        size += ARF_PTR_ALLOC(x) * sizeof(mp_limb_t);

    return size;
}


