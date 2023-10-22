{-|
module      :  Data.Number.Flint.Acb.Calc.FFI
copyright   :  (c) 2022 Hartmut Monien
license     :  GNU GPL, version 2 or above (see LICENSE)
maintainer  :  hmonien@uni-bonn.de
-}
module Data.Number.Flint.Acb.Calc.FFI (
  -- * Calculus with complex-valued functions
  -- * Integration function
    CAcbCalcFunc
  -- * Integration
  , acb_calc_integrate
  -- * Options for integration
  , AcbCalcIntegrateOpt (..)
  , CAcbCalcIntegrateOpt (..)
  , newAcbCalcIntegrateOpt
  , withAcbCalcIntegrateOpt
  , acb_calc_integrate_opt_init
  -- * Local integration algorithms
  , acb_calc_integrate_gl_auto_deg
  -- * Integration (old)
  , acb_calc_cauchy_bound
  , acb_calc_integrate_taylor
) where 

-- Calculus with complex-valued functions --------------------------------------

import Control.Monad

import Foreign.C.String
import Foreign.C.Types
import Foreign.ForeignPtr
import Foreign.Ptr ( Ptr, FunPtr, plusPtr, nullPtr, castPtr )
import Foreign.Storable
import Foreign.Marshal ( free )

import Data.Functor ((<&>))

import Data.Number.Flint.Flint

import Data.Number.Flint.Arb
import Data.Number.Flint.Arb.Types

import Data.Number.Flint.Acb
import Data.Number.Flint.Acb.Types

#include <flint/acb_calc.h>

-- Types, macros and constants -------------------------------------------------

data AcbCalcIntegrateOpt =
  AcbCalcIntegrateOpt {-# UNPACK #-} !(ForeignPtr CAcbCalcIntegrateOpt)
data CAcbCalcIntegrateOpt = CAcbCalcIntegrateOpt CLong CLong CLong CInt CInt

instance Storable CAcbCalcIntegrateOpt where
  sizeOf    _ = #{size      acb_calc_integrate_opt_t}
  alignment _ = #{alignment acb_calc_integrate_opt_t}
  peek ptr = CAcbCalcIntegrateOpt
    <$> #{peek acb_calc_integrate_opt_struct, deg_limit  } ptr
    <*> #{peek acb_calc_integrate_opt_struct, eval_limit } ptr
    <*> #{peek acb_calc_integrate_opt_struct, depth_limit} ptr
    <*> #{peek acb_calc_integrate_opt_struct, use_heap   } ptr
    <*> #{peek acb_calc_integrate_opt_struct, verbose    } ptr
  poke ptr (CAcbCalcIntegrateOpt deg eval depth heap verbose) = do
    (#poke acb_calc_integrate_opt_struct, deg_limit  ) ptr deg
    (#poke acb_calc_integrate_opt_struct, eval_limit ) ptr eval
    (#poke acb_calc_integrate_opt_struct, depth_limit) ptr depth
    (#poke acb_calc_integrate_opt_struct, use_heap   ) ptr heap
    (#poke acb_calc_integrate_opt_struct, verbose    ) ptr verbose
    
newAcbCalcIntegrateOpt = do
  x <- mallocForeignPtr
  withForeignPtr x acb_calc_integrate_opt_init
  return $ AcbCalcIntegrateOpt x

withAcbCalcIntegrateOpt (AcbCalcIntegrateOpt x) f =
  withForeignPtr x $ \xp -> f xp <&> (AcbCalcIntegrateOpt x,)
  
-- acb_calc_func_t -------------------------------------------------------------

type CAcbCalcFunc = Ptr CAcb -> Ptr () -> CLong -> CLong

-- Integration -----------------------------------------------------------------

-- | /acb_calc_integrate/ /res/ /func/ /param/ /a/ /b/ /rel_goal/ /abs_tol/ /options/ /prec/ 
--
-- Computes a rigorous enclosure of the integral
-- 
-- \[`\]
-- \[I = \int_a^b f(t) dt\]
-- 
-- where /f/ is specified by (/func/, /param/), following a straight-line
-- path between the complex numbers /a/ and /b/. For finite results, /a/,
-- /b/ must be finite and /f/ must be bounded on the path of integration.
-- To compute improper integrals, the user should therefore truncate the
-- path of integration manually (or make a regularizing change of
-- variables, if possible). Returns /ARB_CALC_SUCCESS/ if the integration
-- converged to the target accuracy on all subintervals, and returns
-- /ARB_CALC_NO_CONVERGENCE/ otherwise.
-- 
-- By default, the integrand /func/ will only be called with /order/ = 0 or
-- /order/ = 1; that is, derivatives are not required.
-- 
-- -   The integrand will be called with /order/ = 0 to evaluate /f/
--     normally on the integration path (either at a single point or on a
--     subinterval). In this case, /f/ is treated as a pointwise defined
--     function and can have arbitrary discontinuities.
-- -   The integrand will be called with /order/ = 1 to evaluate /f/ on a
--     domain surrounding a segment of the integration path for the purpose
--     of bounding the error of a quadrature formula. In this case, /func/
--     must verify that /f/ is holomorphic on this domain (and output a
--     non-finite value if it is not).
-- 
-- The integration algorithm combines direct interval enclosures,
-- Gauss-Legendre quadrature where /f/ is holomorphic, and adaptive
-- subdivision. This strategy supports integrands with discontinuities
-- while providing exponential convergence for typical piecewise
-- holomorphic integrands.
-- 
-- The following parameters control accuracy:
-- 
-- -   /rel_goal/ - relative accuracy goal as a number of bits, i.e. target
--     a relative error less than \(\varepsilon_{rel} = 2^{-r}\) where /r/
--     = /rel_goal/ (note the sign: /rel_goal/ should be nonnegative).
-- -   /abs_tol/ - absolute accuracy goal as a @mag_t@ describing the error
--     tolerance, i.e. target an absolute error less than
--     \(\varepsilon_{abs}\) = /abs_tol/.
-- -   /prec/ - working precision. This is the working precision used to
--     evaluate the integrand and manipulate interval endpoints. As
--     currently implemented, the algorithm does not attempt to adjust the
--     working precision by itself, and adaptive control of the working
--     precision must be handled by the user.
-- 
-- For typical usage, set /rel_goal/ = /prec/ and /abs_tol/ =
-- \(2^{-prec}\). It usually only makes sense to have /rel_goal/ between 0
-- and /prec/.
-- 
-- The algorithm attempts to achieve an error of
-- \(\max(\varepsilon_{abs}, M \varepsilon_{rel})\) on each subinterval,
-- where /M/ is the magnitude of the integral. These parameters are only
-- guidelines; the cumulative error may be larger than both the prescribed
-- absolute and relative error goals, depending on the number of
-- subdivisions, cancellation between segments of the integral, and
-- numerical errors in the evaluation of the integrand.
-- 
-- To compute tiny integrals with high relative accuracy, one should set
-- \(\varepsilon_{abs} \approx M \varepsilon_{rel}\) where /M/ is a known
-- estimate of the magnitude. Setting \(\varepsilon_{abs}\) to 0 is also
-- allowed, forcing use of a relative instead of an absolute tolerance
-- goal. This can be handy for exponentially small or large functions of
-- unknown magnitude. It is recommended to avoid setting
-- \(\varepsilon_{abs}\) very small if possible since the algorithm might
-- need many extra subdivisions to estimate /M/ automatically; if the
-- approximate magnitude can be estimated by some external means (for
-- example if a midpoint-width or endpoint-width estimate is known to be
-- accurate), providing an appropriate
-- \(\varepsilon_{abs} \approx M \varepsilon_{rel}\) will be more
-- efficient.
-- 
-- If the integral has very large magnitude, setting the absolute tolerance
-- to a corresponding large value is recommended for best performance, but
-- it is not necessary for convergence since the absolute tolerance is
-- increased automatically during the execution of the algorithm if the
-- partial integrals are found to have larger error.
-- 
-- Additional options for the integration can be provided via the /options/
-- parameter (documented below). To use all defaults, /NULL/ can be passed
-- for /options/.
foreign import ccall "acb_calc.h acb_calc_integrate"
  acb_calc_integrate :: Ptr CAcb -> FunPtr CAcbCalcFunc -> Ptr () -> Ptr CAcb -> Ptr CAcb -> CLong -> Ptr CMag -> Ptr CAcbCalcIntegrateOpt -> CLong -> IO CInt

-- Options for integration -----------------------------------------------------

-- | /acb_calc_integrate_opt_init/ /options/ 
--
-- Initializes /options/ for use, setting all fields to 0 indicating
-- default values.
foreign import ccall "acb_calc.h acb_calc_integrate_opt_init"
  acb_calc_integrate_opt_init :: Ptr CAcbCalcIntegrateOpt -> IO ()

-- Local integration algorithms ------------------------------------------------

-- | /acb_calc_integrate_gl_auto_deg/ /res/ /num_eval/ /func/ /param/ /a/ /b/ /tol/ /deg_limit/ /flags/ /prec/ 
--
-- Attempts to compute \(I = \int_a^b f(t) dt\) using a single application
-- of Gauss-Legendre quadrature with automatic determination of the
-- quadrature degree so that the error is smaller than /tol/. Returns
-- /ARB_CALC_SUCCESS/ if the integral has been evaluated successfully or
-- /ARB_CALC_NO_CONVERGENCE/ if the tolerance could not be met. The total
-- number of function evaluations is written to /num_eval/.
-- 
-- For the interval \([-1,1]\), the error of the /n/-point Gauss-Legendre
-- rule is bounded by
-- 
-- \[`\]
-- \[\left| I - \sum_{k=0}^{n-1} w_k f(x_k) \right| \le \frac{64 M}{15 (\rho-1) \rho^{2n-1}}\]
-- 
-- if \(f\) is holomorphic with \(|f(z)| \le M\) inside the ellipse /E/
-- with foci \(\pm 1\) and semiaxes \(X\) and \(Y = \sqrt{X^2 - 1}\) such
-- that \(\rho = X + Y\) with \(\rho > 1\) < [Tre2008]>.
-- 
-- For an arbitrary interval, we use
-- \(\int_a^b f(t) dt = \int_{-1}^1 g(t) dt\) where
-- \(g(t) = \Delta f(\Delta t + m)\), \(\Delta = \tfrac{1}{2}(b-a)\),
-- \(m = \tfrac{1}{2}(a+b)\). With \(I = [\pm X] + [\pm Y]i\), this means
-- that we evaluate \(\Delta f(\Delta I + m)\) to get the bound \(M\). (An
-- improvement would be to reduce the wrapping effect of rotating the
-- ellipse when the path is not rectilinear).
-- 
-- We search for an \(X\) that makes the error small by trying steps
-- \(2^{2^k}\). Larger \(X\) will give smaller \(1 / \rho^{2n-1}\) but
-- larger \(M\). If we try successive larger values of \(k\), we can abort
-- when \(M = \infty\) since this either means that we have hit a
-- singularity or a branch cut or that overestimation in the evaluation of
-- \(f\) is becoming too severe.
foreign import ccall "acb_calc.h acb_calc_integrate_gl_auto_deg"
  acb_calc_integrate_gl_auto_deg :: Ptr CAcb -> Ptr CLong -> FunPtr CAcbCalcFunc -> Ptr () -> Ptr CAcb -> Ptr CAcb -> Ptr CMag -> CLong -> CInt -> CLong -> IO CInt

-- Integration (old) -----------------------------------------------------------

-- | /acb_calc_cauchy_bound/ /bound/ /func/ /param/ /x/ /radius/ /maxdepth/ /prec/ 
--
-- Sets /bound/ to a ball containing the value of the integral
-- 
-- \[`\]
-- \[C(x,r) = \frac{1}{2 \pi r} \oint_{|z-x| = r} |f(z)| dz
--        = \int_0^1 |f(x+re^{2\pi i t})| dt\]
-- 
-- where /f/ is specified by (/func/, /param/) and /r/ is given by
-- /radius/. The integral is computed using a simple step sum. The
-- integration range is subdivided until the order of magnitude of /b/ can
-- be determined (i.e. its error bound is smaller than its midpoint), or
-- until the step length has been cut in half /maxdepth/ times. This
-- function is currently implemented completely naively, and repeatedly
-- subdivides the whole integration range instead of performing adaptive
-- subdivisions.
foreign import ccall "acb_calc.h acb_calc_cauchy_bound"
  acb_calc_cauchy_bound :: Ptr CArb -> FunPtr CAcbCalcFunc -> Ptr () -> Ptr CAcb -> Ptr CArb -> CLong -> CLong -> IO ()

-- | /acb_calc_integrate_taylor/ /res/ /func/ /param/ /a/ /b/ /inner_radius/ /outer_radius/ /accuracy_goal/ /prec/ 
--
-- Computes the integral
-- 
-- \[`\]
-- \[I = \int_a^b f(t) dt\]
-- 
-- where /f/ is specified by (/func/, /param/), following a straight-line
-- path between the complex numbers /a/ and /b/ which both must be finite.
-- 
-- The integral is approximated by piecewise centered Taylor polynomials.
-- Rigorous truncation error bounds are calculated using the Cauchy
-- integral formula. More precisely, if the Taylor series of /f/ centered
-- at the point /m/ is \(f(m+x) = \sum_{n=0}^{\infty} a_n x^n\), then
-- 
-- \[`\]
-- \[\int f(m+x) = \left( \sum_{n=0}^{N-1} a_n \frac{x^{n+1}}{n+1} \right)
--           + \left( \sum_{n=N}^{\infty} a_n \frac{x^{n+1}}{n+1} \right).\]
-- 
-- For sufficiently small /x/, the second series converges and its absolute
-- value is bounded by
-- 
-- \[`\]
-- \[\sum_{n=N}^{\infty} \frac{C(m,R)}{R^n} \frac{|x|^{n+1}}{N+1}
--     = \frac{C(m,R) R x}{(R-x)(N+1)} \left( \frac{x}{R} \right)^N.\]
-- 
-- It is required that any singularities of /f/ are isolated from the path
-- of integration by a distance strictly greater than the positive value
-- /outer_radius/ (which is the integration radius used for the Cauchy
-- bound). Taylor series step lengths are chosen so as not to exceed
-- /inner_radius/, which must be strictly smaller than /outer_radius/ for
-- convergence. A smaller /inner_radius/ gives more rapid convergence of
-- each Taylor series but means that more series might have to be used. A
-- reasonable choice might be to set /inner_radius/ to half the value of
-- /outer_radius/, giving roughly one accurate bit per term.
-- 
-- The truncation point of each Taylor series is chosen so that the
-- absolute truncation error is roughly \(2^{-p}\) where /p/ is given by
-- /accuracy_goal/ (in the future, this might change to a relative
-- accuracy). Arithmetic operations and function evaluations are performed
-- at a precision of /prec/ bits. Note that due to accumulation of
-- numerical errors, both values may have to be set higher (and the
-- endpoints may have to be computed more accurately) to achieve a desired
-- accuracy.
-- 
-- This function chooses the evaluation points uniformly rather than
-- implementing adaptive subdivision.
foreign import ccall "acb_calc.h acb_calc_integrate_taylor"
  acb_calc_integrate_taylor :: Ptr CAcb -> FunPtr CAcbCalcFunc -> Ptr () -> Ptr CAcb -> Ptr CAcb -> Ptr CArf -> Ptr CArf -> CLong -> CLong -> IO CInt

