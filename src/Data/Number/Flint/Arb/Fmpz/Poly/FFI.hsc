module Data.Number.Flint.Arb.Fmpz.Poly.FFI (
  -- * Extra methods for integer polynomials
  -- * Evaluation
    _arb_fmpz_poly_evaluate_arb_horner
  , arb_fmpz_poly_evaluate_arb_horner
  , _arb_fmpz_poly_evaluate_arb_rectangular
  , arb_fmpz_poly_evaluate_arb_rectangular
  , _arb_fmpz_poly_evaluate_arb
  , arb_fmpz_poly_evaluate_arb
  , _arb_fmpz_poly_evaluate_acb_horner
  , arb_fmpz_poly_evaluate_acb_horner
  , _arb_fmpz_poly_evaluate_acb_rectangular
  , arb_fmpz_poly_evaluate_acb_rectangular
  , _arb_fmpz_poly_evaluate_acb
  , arb_fmpz_poly_evaluate_acb
  -- * Utility methods
  , arb_fmpz_poly_deflation
  , arb_fmpz_poly_deflate
  -- * Polynomial roots
  , arb_fmpz_poly_complex_roots
  -- * Special polynomials
  , arb_fmpz_poly_cos_minpoly
  , arb_fmpz_poly_gauss_period_minpoly
) where

-- Extra methods for integer polynomials ---------------------------------------

import Foreign.C.String
import Foreign.C.Types
import Foreign.ForeignPtr
import Foreign.Ptr ( Ptr, FunPtr )
import Foreign.Marshal ( free )

import Foreign.Storable

import Data.Number.Flint.Flint
import Data.Number.Flint.Fmpz
import Data.Number.Flint.Fmpz.Poly
import Data.Number.Flint.Fmpq.Poly

import Data.Number.Flint.Arb
import Data.Number.Flint.Arb.Types
import Data.Number.Flint.Arb.Poly

import Data.Number.Flint.Acb
import Data.Number.Flint.Acb.Types
import Data.Number.Flint.Acb.Poly

-- Evaluation ------------------------------------------------------------------

-- | /_arb_fmpz_poly_evaluate_arb_horner/ /res/ /poly/ /len/ /x/ /prec/ 
--
foreign import ccall "arb_fmpz_poly.h _arb_fmpz_poly_evaluate_arb_horner"
  _arb_fmpz_poly_evaluate_arb_horner :: Ptr CArb -> Ptr CFmpz -> CLong -> Ptr CArb -> CLong -> IO ()

-- | /arb_fmpz_poly_evaluate_arb_horner/ /res/ /poly/ /x/ /prec/ 
--
foreign import ccall "arb_fmpz_poly.h arb_fmpz_poly_evaluate_arb_horner"
  arb_fmpz_poly_evaluate_arb_horner :: Ptr CArb -> Ptr CFmpzPoly -> Ptr CArb -> CLong -> IO ()

-- | /_arb_fmpz_poly_evaluate_arb_rectangular/ /res/ /poly/ /len/ /x/ /prec/ 
--
foreign import ccall "arb_fmpz_poly.h _arb_fmpz_poly_evaluate_arb_rectangular"
  _arb_fmpz_poly_evaluate_arb_rectangular :: Ptr CArb -> Ptr CFmpz -> CLong -> Ptr CArb -> CLong -> IO ()

-- | /arb_fmpz_poly_evaluate_arb_rectangular/ /res/ /poly/ /x/ /prec/ 
--
foreign import ccall "arb_fmpz_poly.h arb_fmpz_poly_evaluate_arb_rectangular"
  arb_fmpz_poly_evaluate_arb_rectangular :: Ptr CArb -> Ptr CFmpzPoly -> Ptr CArb -> CLong -> IO ()

-- | /_arb_fmpz_poly_evaluate_arb/ /res/ /poly/ /len/ /x/ /prec/ 
--
foreign import ccall "arb_fmpz_poly.h _arb_fmpz_poly_evaluate_arb"
  _arb_fmpz_poly_evaluate_arb :: Ptr CArb -> Ptr CFmpz -> CLong -> Ptr CArb -> CLong -> IO ()

-- | /arb_fmpz_poly_evaluate_arb/ /res/ /poly/ /x/ /prec/ 
--
foreign import ccall "arb_fmpz_poly.h arb_fmpz_poly_evaluate_arb"
  arb_fmpz_poly_evaluate_arb :: Ptr CArb -> Ptr CFmpzPoly -> Ptr CArb -> CLong -> IO ()

-- | /_arb_fmpz_poly_evaluate_acb_horner/ /res/ /poly/ /len/ /x/ /prec/ 
--
foreign import ccall "arb_fmpz_poly.h _arb_fmpz_poly_evaluate_acb_horner"
  _arb_fmpz_poly_evaluate_acb_horner :: Ptr CAcb -> Ptr CFmpz -> CLong -> Ptr CAcb -> CLong -> IO ()

-- | /arb_fmpz_poly_evaluate_acb_horner/ /res/ /poly/ /x/ /prec/ 
--
foreign import ccall "arb_fmpz_poly.h arb_fmpz_poly_evaluate_acb_horner"
  arb_fmpz_poly_evaluate_acb_horner :: Ptr CAcb -> Ptr CFmpzPoly -> Ptr CAcb -> CLong -> IO ()

-- | /_arb_fmpz_poly_evaluate_acb_rectangular/ /res/ /poly/ /len/ /x/ /prec/ 
--
foreign import ccall "arb_fmpz_poly.h _arb_fmpz_poly_evaluate_acb_rectangular"
  _arb_fmpz_poly_evaluate_acb_rectangular :: Ptr CAcb -> Ptr CFmpz -> CLong -> Ptr CAcb -> CLong -> IO ()

-- | /arb_fmpz_poly_evaluate_acb_rectangular/ /res/ /poly/ /x/ /prec/ 
--
foreign import ccall "arb_fmpz_poly.h arb_fmpz_poly_evaluate_acb_rectangular"
  arb_fmpz_poly_evaluate_acb_rectangular :: Ptr CAcb -> Ptr CFmpzPoly -> Ptr CAcb -> CLong -> IO ()

-- | /_arb_fmpz_poly_evaluate_acb/ /res/ /poly/ /len/ /x/ /prec/ 
--
foreign import ccall "arb_fmpz_poly.h _arb_fmpz_poly_evaluate_acb"
  _arb_fmpz_poly_evaluate_acb :: Ptr CAcb -> Ptr CFmpz -> CLong -> Ptr CAcb -> CLong -> IO ()

-- | /arb_fmpz_poly_evaluate_acb/ /res/ /poly/ /x/ /prec/ 
--
-- Evaluates /poly/ (given by a polynomial object or an array with /len/
-- coefficients) at the given real or complex number, respectively using
-- Horner\'s rule, rectangular splitting, or a default algorithm choice.
foreign import ccall "arb_fmpz_poly.h arb_fmpz_poly_evaluate_acb"
  arb_fmpz_poly_evaluate_acb :: Ptr CAcb -> Ptr CFmpzPoly -> Ptr CAcb -> CLong -> IO ()

-- Utility methods -------------------------------------------------------------

-- | /arb_fmpz_poly_deflation/ /poly/ 
--
-- Finds the maximal exponent by which /poly/ can be deflated.
foreign import ccall "arb_fmpz_poly.h arb_fmpz_poly_deflation"
  arb_fmpz_poly_deflation :: Ptr CFmpzPoly -> IO CULong

-- | /arb_fmpz_poly_deflate/ /res/ /poly/ /deflation/ 
--
-- Sets /res/ to a copy of /poly/ deflated by the exponent /deflation/.
foreign import ccall "arb_fmpz_poly.h arb_fmpz_poly_deflate"
  arb_fmpz_poly_deflate :: Ptr CFmpzPoly -> Ptr CFmpzPoly -> CULong -> IO ()

-- Polynomial roots ------------------------------------------------------------

-- | /arb_fmpz_poly_complex_roots/ /roots/ /poly/ /flags/ /prec/ 
--
-- Writes to /roots/ all the real and complex roots of the polynomial
-- /poly/, computed to at least /prec/ accurate bits. The root enclosures
-- are guaranteed to be disjoint, so that all roots are isolated.
-- 
-- The real roots are written first in ascending order (with the imaginary
-- parts set exactly to zero). The following nonreal roots are written in
-- arbitrary order, but with conjugate pairs grouped together (the root in
-- the upper plane leading the root in the lower plane).
-- 
-- The input polynomial /must/ be squarefree. For a general polynomial,
-- compute the squarefree part \(f / \gcd(f,f')\) or do a full squarefree
-- factorization to obtain the multiplicities of the roots:
-- 
-- > fmpz_poly_factor_t fac;
-- > fmpz_poly_factor_init(fac);
-- > fmpz_poly_factor_squarefree(fac, poly);
-- >
-- > for (i = 0; i < fac->num; i++)
-- > {
-- >     deg = fmpz_poly_degree(fac->p + i);
-- >     flint_printf("%wd roots of multiplicity %wd\n", deg, fac->exp[i]);
-- >     roots = _acb_vec_init(deg);
-- >     arb_fmpz_poly_complex_roots(roots, fac->p + i, 0, prec);
-- >     _acb_vec_clear(roots, deg);
-- > }
-- >
-- > fmpz_poly_factor_clear(fac);
-- 
-- All roots are refined to a relative accuracy of at least /prec/ bits.
-- The output values will generally have higher actual precision, depending
-- on the precision needed for isolation and the precision used internally
-- by the algorithm.
-- 
-- This implementation should be adequate for general use, but it is not
-- currently competitive with state-of-the-art isolation methods for
-- finding real roots alone.
-- 
-- The following /flags/ are supported:
-- 
-- -   /ARB_FMPZ_POLY_ROOTS_VERBOSE/
foreign import ccall "arb_fmpz_poly.h arb_fmpz_poly_complex_roots"
  arb_fmpz_poly_complex_roots :: Ptr CAcb -> Ptr CFmpzPoly -> CInt -> CLong -> IO ()

-- Special polynomials ---------------------------------------------------------

-- Note: see also the methods available in FLINT (e.g. for cyclotomic
-- polynomials).
--
-- | /arb_fmpz_poly_cos_minpoly/ /res/ /n/ 
--
-- Sets /res/ to the monic minimal polynomial of \(2 \cos(2 \pi / n)\).
-- This is a wrapper of FLINT\'s /fmpz_poly_cos_minpoly/, provided here for
-- backward compatibility.
foreign import ccall "arb_fmpz_poly.h arb_fmpz_poly_cos_minpoly"
  arb_fmpz_poly_cos_minpoly :: Ptr CFmpzPoly -> CULong -> IO ()

-- | /arb_fmpz_poly_gauss_period_minpoly/ /res/ /q/ /n/ 
--
-- Sets /res/ to the minimal polynomial of the Gaussian periods
-- \(\sum_{a \in H} \zeta^a\) where \(\zeta = \exp(2 \pi i / q)\) and /H/
-- are the cosets of the subgroups of order \(d = (q - 1) / n\) of
-- \((\mathbb{Z}/q\mathbb{Z})^{\times}\). The resulting polynomial has
-- degree /n/. When \(d = 1\), the result is the cyclotomic polynomial
-- \(\Phi_q\).
-- 
-- The implementation assumes that /q/ is prime, and that /n/ is a divisor
-- of \(q - 1\) such that /n/ is coprime with /d/. If any condition is not
-- met, /res/ is set to the zero polynomial.
-- 
-- This method provides a fast (in practice) way to construct finite field
-- extensions of prescribed degree. If /q/ satisfies the conditions stated
-- above and \((q-1)/f\) additionally is coprime with /n/, where /f/ is the
-- multiplicative order of /p/ mod /q/, then the Gaussian period minimal
-- polynomial is irreducible over \(\operatorname{GF}(p)\) < [CP2005]>.
foreign import ccall "arb_fmpz_poly.h arb_fmpz_poly_gauss_period_minpoly"
  arb_fmpz_poly_gauss_period_minpoly :: Ptr CFmpzPoly -> CULong -> CULong -> IO ()

