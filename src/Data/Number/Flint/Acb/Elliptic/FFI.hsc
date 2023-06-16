module Data.Number.Flint.Acb.Elliptic.FFI (
  -- * Elliptic integrals and functions of complex variables
  -- * Complete elliptic integrals
    acb_elliptic_k
  , acb_elliptic_k_jet
  , _acb_elliptic_k_series
  , acb_elliptic_k_series
  , acb_elliptic_e
  , acb_elliptic_pi
  -- * Legendre incomplete elliptic integrals
  , acb_elliptic_f
  , acb_elliptic_e_inc
  , acb_elliptic_pi_inc
  -- * Carlson symmetric elliptic integrals
  , acb_elliptic_rf
  , acb_elliptic_rg
  , acb_elliptic_rj
  , acb_elliptic_rj_carlson
  , acb_elliptic_rj_integration
  , acb_elliptic_rc1
  -- * Weierstrass elliptic functions
  , acb_elliptic_p
  , acb_elliptic_p_prime
  , acb_elliptic_p_jet
  , _acb_elliptic_p_series
  , acb_elliptic_p_series
  , acb_elliptic_invariants
  , acb_elliptic_roots
  , acb_elliptic_inv_p
  , acb_elliptic_zeta
  , acb_elliptic_sigma
) where

-- Elliptic integrals and functions of complex variables -----------------------

import Foreign.Ptr
import Foreign.C.Types
import Foreign.C.String

import Data.Number.Flint.Arb.Types
import Data.Number.Flint.Acb.Types
import Data.Number.Flint.Acb.Poly

-- Complete elliptic integrals -------------------------------------------------

-- | /acb_elliptic_k/ /res/ /m/ /prec/ 
-- 
-- Computes the complete elliptic integral of the first kind
-- 
-- \[`\]
-- \[K(m) = \int_0^{\pi/2} \frac{dt}{\sqrt{1-m \sin^2 t}}
--           = \int_0^1
--     \frac{dt}{\left(\sqrt{1-t^2}\right)\left(\sqrt{1-mt^2}\right)}\]
-- 
-- using the arithmetic-geometric mean: \(K(m) = \pi / (2 M(\sqrt{1-m}))\).
foreign import ccall "acb_elliptic.h acb_elliptic_k"
  acb_elliptic_k :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_elliptic_k_jet/ /res/ /m/ /len/ /prec/ 
-- 
-- Sets the coefficients in the array /res/ to the power series expansion
-- of the complete elliptic integral of the first kind at the point /m/
-- truncated to length /len/, i.e. \(K(m+x) \in \mathbb{C}[[x]]\).
foreign import ccall "acb_elliptic.h acb_elliptic_k_jet"
  acb_elliptic_k_jet :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> IO ()

foreign import ccall "acb_elliptic.h _acb_elliptic_k_series"
  _acb_elliptic_k_series :: Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> CLong -> IO ()

-- | /acb_elliptic_k_series/ /res/ /m/ /len/ /prec/ 
-- 
-- Sets /res/ to the complete elliptic integral of the first kind of the
-- power series /m/, truncated to length /len/.
foreign import ccall "acb_elliptic.h acb_elliptic_k_series"
  acb_elliptic_k_series :: Ptr CAcbPoly -> Ptr CAcbPoly -> CLong -> CLong -> IO ()

-- | /acb_elliptic_e/ /res/ /m/ /prec/ 
-- 
-- Computes the complete elliptic integral of the second kind
-- 
-- \[`\]
-- \[E(m) = \int_0^{\pi/2} \sqrt{1-m \sin^2 t} \, dt =
--             \int_0^1
--             \frac{\sqrt{1-mt^2}}{\sqrt{1-t^2}} \, dt\]
-- 
-- using \(E(m) = (1-m)(2m K'(m) + K(m))\) (where the prime denotes a
-- derivative, not a complementary integral).
foreign import ccall "acb_elliptic.h acb_elliptic_e"
  acb_elliptic_e :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_elliptic_pi/ /res/ /n/ /m/ /prec/ 
-- 
-- Evaluates the complete elliptic integral of the third kind
-- 
-- \[`\]
-- \[\Pi(n, m) = \int_0^{\pi/2}
--     \frac{dt}{(1-n \sin^2 t) \sqrt{1-m \sin^2 t}} =
--     \int_0^1
--     \frac{dt}{(1-nt^2) \sqrt{1-t^2} \sqrt{1-mt^2}}.\]
-- 
-- This implementation currently uses the same algorithm as the
-- corresponding incomplete integral. It is therefore less efficient than
-- the implementations of the first two complete elliptic integrals which
-- use the AGM.
foreign import ccall "acb_elliptic.h acb_elliptic_pi"
  acb_elliptic_pi :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- Legendre incomplete elliptic integrals --------------------------------------

-- | /acb_elliptic_f/ /res/ /phi/ /m/ /pi/ /prec/ 
-- 
-- Evaluates the Legendre incomplete elliptic integral of the first kind,
-- given by
-- 
-- \[`\]
-- \[F(\phi,m) = \int_0^{\phi} \frac{dt}{\sqrt{1-m \sin^2 t}}
--           = \int_0^{\sin \phi}
--     \frac{dt}{\left(\sqrt{1-t^2}\right)\left(\sqrt{1-mt^2}\right)}\]
-- 
-- on the standard strip \(-\pi/2 \le \operatorname{Re}(\phi) \le \pi/2\).
-- Outside this strip, the function extends quasiperiodically as
-- 
-- \[`\]
-- \[F(\phi + n \pi, m) = 2 n K(m) + F(\phi,m), n \in \mathbb{Z}.\]
-- 
-- Inside the standard strip, the function is computed via the symmetric
-- integral \(R_F\).
-- 
-- If the flag /pi/ is set to 1, the variable \(\phi\) is replaced by
-- \(\pi \phi\), changing the quasiperiod to 1.
-- 
-- The function reduces to a complete elliptic integral of the first kind
-- when \(\phi = \frac{\pi}{2}\); that is,
-- \(F\left(\frac{\pi}{2}, m\right) = K(m)\).
foreign import ccall "acb_elliptic.h acb_elliptic_f"
  acb_elliptic_f :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CInt -> CLong -> IO ()

-- | /acb_elliptic_e_inc/ /res/ /phi/ /m/ /pi/ /prec/ 
-- 
-- Evaluates the Legendre incomplete elliptic integral of the second kind,
-- given by
-- 
-- \[`\]
-- \[E(\phi,m) = \int_0^{\phi} \sqrt{1-m \sin^2 t} \, dt =
--             \int_0^{\sin \phi}
--             \frac{\sqrt{1-mt^2}}{\sqrt{1-t^2}} \, dt\]
-- 
-- on the standard strip \(-\pi/2 \le \operatorname{Re}(\phi) \le \pi/2\).
-- Outside this strip, the function extends quasiperiodically as
-- 
-- \[`\]
-- \[E(\phi + n \pi, m) = 2 n E(m) + E(\phi,m), n \in \mathbb{Z}.\]
-- 
-- Inside the standard strip, the function is computed via the symmetric
-- integrals \(R_F\) and \(R_D\).
-- 
-- If the flag /pi/ is set to 1, the variable \(\phi\) is replaced by
-- \(\pi \phi\), changing the quasiperiod to 1.
-- 
-- The function reduces to a complete elliptic integral of the second kind
-- when \(\phi = \frac{\pi}{2}\); that is,
-- \(E\left(\frac{\pi}{2}, m\right) = E(m)\).
foreign import ccall "acb_elliptic.h acb_elliptic_e_inc"
  acb_elliptic_e_inc :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CInt -> CLong -> IO ()

-- | /acb_elliptic_pi_inc/ /res/ /n/ /phi/ /m/ /pi/ /prec/ 
-- 
-- Evaluates the Legendre incomplete elliptic integral of the third kind,
-- given by
-- 
-- \[`\]
-- \[\Pi(n, \phi, m) = \int_0^{\phi}
--     \frac{dt}{(1-n \sin^2 t) \sqrt{1-m \sin^2 t}} =
--     \int_0^{\sin \phi}
--     \frac{dt}{(1-nt^2) \sqrt{1-t^2} \sqrt{1-mt^2}}\]
-- 
-- on the standard strip \(-\pi/2 \le \operatorname{Re}(\phi) \le \pi/2\).
-- Outside this strip, the function extends quasiperiodically as
-- 
-- \[`\]
-- \[\Pi(n, \phi + k \pi, m) = 2 k \Pi(n,m) + \Pi(n,\phi,m), k \in \mathbb{Z}.\]
-- 
-- Inside the standard strip, the function is computed via the symmetric
-- integrals \(R_F\) and \(R_J\).
-- 
-- If the flag /pi/ is set to 1, the variable \(\phi\) is replaced by
-- \(\pi \phi\), changing the quasiperiod to 1.
-- 
-- The function reduces to a complete elliptic integral of the third kind
-- when \(\phi = \frac{\pi}{2}\); that is,
-- \(\Pi\left(n, \frac{\pi}{2}, m\right) = \Pi(n, m)\).
foreign import ccall "acb_elliptic.h acb_elliptic_pi_inc"
  acb_elliptic_pi_inc :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CInt -> CLong -> IO ()

-- Carlson symmetric elliptic integrals ----------------------------------------

-- Carlson symmetric forms are the preferred form of incomplete elliptic
-- integrals, due to their neat properties and relatively simple
-- computation based on duplication theorems. There are five named
-- functions: \(R_F, R_G, R_J\), and \(R_C\), \(R_D\) which are special
-- cases of \(R_F\) and \(R_J\) respectively. We largely follow the
-- definitions and algorithms in < [Car1995]> and chapter 19 in
-- < [NIST2012]>.
--
-- | /acb_elliptic_rf/ /res/ /x/ /y/ /z/ /flags/ /prec/ 
-- 
-- Evaluates the Carlson symmetric elliptic integral of the first kind
-- 
-- \[`\]
-- \[R_F(x,y,z) = \frac{1}{2}
--     \int_0^{\infty} \frac{dt}{\sqrt{(t+x)(t+y)(t+z)}}\]
-- 
-- where the square root extends continuously from positive infinity. The
-- integral is well-defined for \(x,y,z \notin (-\infty,0)\), and with at
-- most one of \(x,y,z\) being zero. When some parameters are negative real
-- numbers, the function is still defined by analytic continuation.
-- 
-- In general, one or more duplication steps are applied until \(x,y,z\)
-- are close enough to use a multivariate Taylor series.
-- 
-- The special case
-- \(R_C(x, y) = R_F(x, y, y) = \frac{1}{2} \int_0^{\infty} (t+x)^{-1/2} (t+y)^{-1} dt\)
-- may be computed by setting /y/ and /z/ to the same variable. (This case
-- is not yet handled specially, but might be optimized in the future.)
-- 
-- The /flags/ parameter is reserved for future use and currently does
-- nothing. Passing 0 results in default behavior.
foreign import ccall "acb_elliptic.h acb_elliptic_rf"
  acb_elliptic_rf :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CInt -> CLong -> IO ()

-- | /acb_elliptic_rg/ /res/ /x/ /y/ /z/ /flags/ /prec/ 
-- 
-- Evaluates the Carlson symmetric elliptic integral of the second kind
-- 
-- \[`\]
-- \[R_G(x,y,z) = \frac{1}{4} \int_0^{\infty}
--     \frac{t}{\sqrt{(t+x)(t+y)(t+z)}}
--     \left( \frac{x}{t+x} + \frac{y}{t+y} + \frac{z}{t+z}\right) dt\]
-- 
-- where the square root is taken continuously as in \(R_F\). The
-- evaluation is done by expressing \(R_G\) in terms of \(R_F\) and
-- \(R_D\). There are no restrictions on the variables.
foreign import ccall "acb_elliptic.h acb_elliptic_rg"
  acb_elliptic_rg :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CInt -> CLong -> IO ()

foreign import ccall "acb_elliptic.h acb_elliptic_rj"
  acb_elliptic_rj :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CInt -> CLong -> IO ()

foreign import ccall "acb_elliptic.h acb_elliptic_rj_carlson"
  acb_elliptic_rj_carlson :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CInt -> CLong -> IO ()

-- | /acb_elliptic_rj_integration/ /res/ /x/ /y/ /z/ /p/ /flags/ /prec/ 
-- 
-- Evaluates the Carlson symmetric elliptic integral of the third kind
-- 
-- \[`\]
-- \[R_J(x,y,z,p) = \frac{3}{2}
--     \int_0^{\infty} \frac{dt}{(t+p)\sqrt{(t+x)(t+y)(t+z)}}\]
-- 
-- where the square root is taken continuously as in \(R_F\).
-- 
-- Three versions of this function are available: the /carlson/ version
-- applies one or more duplication steps until \(x,y,z,p\) are close enough
-- to use a multivariate Taylor series.
-- 
-- The duplication algorithm is not correct for all possible combinations
-- of complex variables, since the square roots taken during the
-- computation can introduce spurious branch cuts. According to
-- < [Car1995]>, a sufficient (but not necessary) condition for correctness
-- is that /x/, /y/, /z/ have nonnegative real part and that /p/ has
-- positive real part.
-- 
-- In other cases, the algorithm /might/ still be correct, but no attempt
-- is made to check this; it is up to the user to verify that the
-- duplication algorithm is appropriate for the given parameters before
-- calling this function.
-- 
-- The /integration/ algorithm uses explicit numerical integration to
-- translate the parameters to the right half-plane. This is reliable but
-- can be slow.
-- 
-- The default method uses the /carlson/ algorithm when it is certain to be
-- correct, and otherwise falls back to the slow /integration/ algorithm.
-- 
-- The special case \(R_D(x, y, z) = R_J(x, y, z, z)\) may be computed by
-- setting /z/ and /p/ to the same variable. This case is handled specially
-- to avoid redundant arithmetic operations. In this case, the /carlson/
-- algorithm is correct for all /x/, /y/ and /z/.
-- 
-- The /flags/ parameter is reserved for future use and currently does
-- nothing. Passing 0 results in default behavior.
foreign import ccall "acb_elliptic.h acb_elliptic_rj_integration"
  acb_elliptic_rj_integration :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CInt -> CLong -> IO ()

-- | /acb_elliptic_rc1/ /res/ /x/ /prec/ 
-- 
-- This helper function computes the special case
-- \(R_C(1, 1+x) = \operatorname{atan}(\sqrt{x})/\sqrt{x} = {}_2F_1(1,1/2,3/2,-x)\),
-- which is needed in the evaluation of \(R_J\).
foreign import ccall "acb_elliptic.h acb_elliptic_rc1"
  acb_elliptic_rc1 :: Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- Weierstrass elliptic functions ----------------------------------------------

-- Elliptic functions may be defined on a general lattice Lambda = {m
-- 2omega_1 + n 2omega_2: m, n in mathbb{Z}} with half-periods
-- \(\omega_1, \omega_2\). We simplify by setting 2omega_1 = 1, 2omega_2 =
-- tau with \(\operatorname{im}(\tau) > 0\). To evaluate the functions on a
-- general lattice, it is enough to make a linear change of variables. The
-- main reference is chapter 23 in < [NIST2012]>.
--
-- | /acb_elliptic_p/ /res/ /z/ /tau/ /prec/ 
-- 
-- Computes Weierstrass\'s elliptic function
-- 
-- \[`\]
-- \[\wp(z, \tau) = \frac{1}{z^2} + \sum_{n^2+m^2 \ne 0}
--     \left[ \frac{1}{(z+m+n\tau)^2} - \frac{1}{(m+n\tau)^2} \right]\]
-- 
-- which satisfies
-- \(\wp(z, \tau) = \wp(z + 1, \tau) = \wp(z + \tau, \tau)\). To evaluate
-- the function efficiently, we use the formula
-- 
-- \[`\]
-- \[\wp(z, \tau) = \pi^2 \theta_2^2(0,\tau) \theta_3^2(0,\tau)
--     \frac{\theta_4^2(z,\tau)}{\theta_1^2(z,\tau)} -
--     \frac{\pi^2}{3} \left[ \theta_2^4(0,\tau) + \theta_3^4(0,\tau)\right].\]
foreign import ccall "acb_elliptic.h acb_elliptic_p"
  acb_elliptic_p :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_elliptic_p_prime/ /res/ /z/ /tau/ /prec/ 
-- 
-- Computes the derivative \(\wp'(z, \tau)\) of Weierstrass\'s elliptic
-- function \(\wp(z, \tau)\).
foreign import ccall "acb_elliptic.h acb_elliptic_p_prime"
  acb_elliptic_p_prime :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_elliptic_p_jet/ /res/ /z/ /tau/ /len/ /prec/ 
-- 
-- Computes the formal power series
-- \(\wp(z + x, \tau) \in \mathbb{C}[[x]]\), truncated to length /len/. In
-- particular, with /len/ = 2, simultaneously computes
-- \(\wp(z, \tau), \wp'(z, \tau)\) which together generate the field of
-- elliptic functions with periods 1 and \(\tau\).
foreign import ccall "acb_elliptic.h acb_elliptic_p_jet"
  acb_elliptic_p_jet :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> CLong -> IO ()

foreign import ccall "acb_elliptic.h _acb_elliptic_p_series"
  _acb_elliptic_p_series :: Ptr CAcb -> Ptr CAcb -> CLong -> Ptr CAcb -> CLong -> CLong -> IO ()

-- | /acb_elliptic_p_series/ /res/ /z/ /tau/ /len/ /prec/ 
-- 
-- Sets /res/ to the Weierstrass elliptic function of the power series /z/,
-- with periods 1 and /tau/, truncated to length /len/.
foreign import ccall "acb_elliptic.h acb_elliptic_p_series"
  acb_elliptic_p_series :: Ptr CAcbPoly -> Ptr CAcbPoly -> Ptr CAcb -> CLong -> CLong -> IO ()

-- | /acb_elliptic_invariants/ /g2/ /g3/ /tau/ /prec/ 
-- 
-- Computes the lattice invariants \(g_2, g_3\). The Weierstrass elliptic
-- function satisfies the differential equation
-- \([\wp'(z, \tau)]^2 = 4 [\wp(z,\tau)]^3 - g_2 \wp(z,\tau) - g_3\). Up to
-- constant factors, the lattice invariants are the first two Eisenstein
-- series (see @acb_modular_eisenstein@).
foreign import ccall "acb_elliptic.h acb_elliptic_invariants"
  acb_elliptic_invariants :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_elliptic_roots/ /e1/ /e2/ /e3/ /tau/ /prec/ 
-- 
-- Computes the lattice roots \(e_1, e_2, e_3\), which are the roots of the
-- polynomial \(4z^3 - g_2 z - g_3\).
foreign import ccall "acb_elliptic.h acb_elliptic_roots"
  acb_elliptic_roots :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_elliptic_inv_p/ /res/ /z/ /tau/ /prec/ 
-- 
-- Computes the inverse of the Weierstrass elliptic function, which
-- satisfies \(\wp(\wp^{-1}(z, \tau), \tau) = z\). This function is given
-- by the elliptic integral
-- 
-- \[`\]
-- \[\wp^{-1}(z, \tau) = \frac{1}{2} \int_z^{\infty} \frac{dt}{\sqrt{(t-e_1)(t-e_2)(t-e_3)}}
--     = R_F(z-e_1,z-e_2,z-e_3).\]
foreign import ccall "acb_elliptic.h acb_elliptic_inv_p"
  acb_elliptic_inv_p :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_elliptic_zeta/ /res/ /z/ /tau/ /prec/ 
-- 
-- Computes the Weierstrass zeta function
-- 
-- \[`\]
-- \[\zeta(z, \tau) = \frac{1}{z} + \sum_{n^2+m^2 \ne 0}
--     \left[ \frac{1}{z-m-n\tau} + \frac{1}{m+n\tau} + \frac{z}{(m+n\tau)^2} \right]\]
-- 
-- which is quasiperiodic with
-- \(\zeta(z + 1, \tau) = \zeta(z, \tau) + \zeta(1/2, \tau)\) and
-- \(\zeta(z + \tau, \tau) = \zeta(z, \tau) + \zeta(\tau/2, \tau)\).
foreign import ccall "acb_elliptic.h acb_elliptic_zeta"
  acb_elliptic_zeta :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

-- | /acb_elliptic_sigma/ /res/ /z/ /tau/ /prec/ 
-- 
-- Computes the Weierstrass sigma function
-- 
-- \[`\]
-- \[\sigma(z, \tau) = z \prod_{n^2+m^2 \ne 0}
--     \left[ \left(1-\frac{z}{m+n\tau}\right)
--        \exp\left(\frac{z}{m+n\tau} + \frac{z^2}{2(m+n\tau)^2} \right) \right]\]
-- 
-- which is quasiperiodic with
-- \(\sigma(z + 1, \tau) = -e^{2 \zeta(1/2, \tau) (z+1/2)} \sigma(z, \tau)\)
-- and
-- \(\sigma(z + \tau, \tau) = -e^{2 \zeta(\tau/2, \tau) (z+\tau/2)} \sigma(z, \tau)\).
foreign import ccall "acb_elliptic.h acb_elliptic_sigma"
  acb_elliptic_sigma :: Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> IO ()

