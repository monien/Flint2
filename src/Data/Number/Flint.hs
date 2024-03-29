{-|
module      :  Data.Number.Flint.Flint
copyright   :  (c) 2022 Hartmut Monien
license     :  GNU GPL, version 2 or above (see LICENSE)
maintainer  :  hmonien@uni-bonn.de

= What is FLINT ?

FLINT is a C library for doing number theory, freely available under the GNU LGPL at [https://flintlib.org](https://flintlib.org)

Some domains handled by FLINT are \(\mathbb{Z}\), \(\mathbb{Q}\), \(\mathbb{F}_q\), \(\overline{\mathbb{Q}}\), \(\mathbb{C}\) and \(Q[x,y,z]\).
At its core, FLINT provides arithmetic
in standard rings such as the integers, rationals, algebraic, real,
complex and p-adic numbers, finite fields, and number fields. It also
provides polynomials (univariate and multivariate), power series, and
matrices.

FLINT covers a wide range of functionality: primality testing, integer factorisation, multivariate polynomial GCD and factorisation, FFTs, multimodular reconstruction, special functions, exact and approximate linear algebra, LLL, finite field embeddings, and more.

= Mature & widely used

FLINT is the work of dozens of contributors, spanning 15+ years of development. The upcoming FLINT 3.0 release comprises 8,000 documented functions, 3,500 test programs, and 900,000 lines of code.

FLINT runs on most common platforms, including Linux, macOS and Windows on typical hardware configurations. Several computer algebra systems rely on FLINT as a back-end library, including SageMath, Oscar, Singular, Macaulay2, Maple and Mathematica. Wrappers are also available for various programming languages, including Python and Julia.

= At the research frontier

FLINT has been used for many large scale research computations (for example: A Trillion Triangles) and has been cited in hundreds of publications. FLINT's authors themselves have published more than 20 papers describing new algorithms first implemented within or on top of FLINT.

= Efficient

FLINT is designed for all operand sizes, from single-word to multi-gigabyte. It implements many low-level optimisations and chooses automatically between basecase, intermediate, asymptotically fast and special-purpose algorithms depending on the size and structure of the problem. Many algorithms are fully parallel (multithreaded) and some key functions use SIMD acceleration.

= Handles real numbers

<<docs/out.png>> 

FLINT has advanced support for real and complex numbers, implemented using ball arithmetic. It covers a variety of numerical functionality (polynomial arithmetic, transcendental functions, numerical integration, linear algebra, etc.) with arbitrary precision and with rigorous error bounds. FLINT also provides an exact (symbolic) model of real and complex numbers with the ability to decide equalities.

= Developer-friendly

FLINT has a developer-friendly GMP-like C API which makes it easy to write performant and type-safe code with fine-grained control over in-place mutations, memory allocation, precision, conversions between representations, and algorithm parameters. FLINT also provides well-documented access to most of its internals. Finally, the FLINT project is developed openly in collaboration with the community, and welcomes contributions (feature requests, bug reports, patches, testing, documentation, general feedback) from anyone.

Note: this functionality is new in FLINT 3.0 and is due to merging the spin-off projects Arb, Antic and Calcium which were previously maintained as standalone libraries.

= Now this functionality is also available in Haskell!

The modules in `Data.Number.Flint` provide a access to most of the
functionality in @flintlib@. Many of the data structures have been
translated to Haskell.  Typically an object of type __x_t__ in flint
will be called __X__ and can be created with a function name __newX__
and a applied to a flint function with a __withX__ function. E.g. the
integers in flint with the type `Fmpz` will be created in the IO
monad using `newFmpz` and used with the `withFmpz` function.

 -}

module Data.Number.Flint (
  module Data.Number.Flint.Flint
, module Data.Number.Flint.UFD
, module Data.Number.Flint.Quotient
, module Data.Number.Flint.MPoly
-- * Integers
, module Data.Number.Flint.Fmpz
-- ** Factorization of integers
, module Data.Number.Flint.Fmpz.Factor
-- ** Arithmtic and special functions for integers
, module Data.Number.Flint.Fmpz.Arith
, module Data.Number.Flint.Fmpz.Vec
, module Data.Number.Flint.Fmpz.Mat
, module Data.Number.Flint.Fmpz.Poly
, module Data.Number.Flint.Fmpz.Poly.Instances
, module Data.Number.Flint.Fmpz.Poly.Mat
, module Data.Number.Flint.Fmpz.Poly.Factor
, module Data.Number.Flint.Fmpz.Poly.Q
, module Data.Number.Flint.Fmpz.MPoly
, module Data.Number.Flint.Fmpz.MPoly.Factor
, module Data.Number.Flint.Fmpz.MPoly.Q
, module Data.Number.Flint.Fmpz.LLL
-- ** Integers mod n
, module Data.Number.Flint.Fmpz.Mod
, module Data.Number.Flint.Fmpz.Mod.Poly
, module Data.Number.Flint.Fmpz.Mod.Poly.Factor
, module Data.Number.Flint.Fmpz.Mod.MPoly
, module Data.Number.Flint.Fmpz.Mod.MPoly.Factor
, module Data.Number.Flint.Fmpz.Mod.Mat
-- * Rational numbers
, module Data.Number.Flint.Fmpq
, module Data.Number.Flint.Fmpq.Mat
, module Data.Number.Flint.Fmpq.Vec
, module Data.Number.Flint.Fmpq.Poly
, module Data.Number.Flint.Fmpq.MPoly
, module Data.Number.Flint.Fmpq.MPoly.Factor
-- * APRCL primality testing
, module Data.Number.Flint.APRCL
-- * FFT
, module Data.Number.Flint.FFT
--, module Data.Number.Flint.FFT.Small
-- * Quadratic sieve
, module Data.Number.Flint.QSieve
-- * Integers mod n
, module Data.Number.Flint.NMod
, module Data.Number.Flint.NMod.Poly
, module Data.Number.Flint.NMod.Poly.Factor
, module Data.Number.Flint.NMod.Poly.Mat
, module Data.Number.Flint.NMod.MPoly
, module Data.Number.Flint.NMod.MPoly.Factor
, module Data.Number.Flint.NMod.Mat
, module Data.Number.Flint.NMod.Vec
-- * Groups and other structures
, module Data.Number.Flint.Groups.Perm
, module Data.Number.Flint.Groups.Qfb
, module Data.Number.Flint.Groups.Dirichlet
, module Data.Number.Flint.Groups.DLog
, module Data.Number.Flint.Groups.Bool.Mat
-- * Number fields and algebraic numbers
, module Data.Number.Flint.NF
, module Data.Number.Flint.NF.Elem
, module Data.Number.Flint.NF.Fmpzi
, module Data.Number.Flint.NF.QQbar
-- * Real and complex numbers
-- ** Real
, module Data.Number.Flint.Arb
, module Data.Number.Flint.Arb.RealField
, module Data.Number.Flint.Arb.Mag
, module Data.Number.Flint.Arb.Mag.Instances
, module Data.Number.Flint.Arb.Arf
, module Data.Number.Flint.Arb.Poly
, module Data.Number.Flint.Arb.Fmpz.Poly
, module Data.Number.Flint.Arb.Mat
, module Data.Number.Flint.Arb.Hypgeom
, module Data.Number.Flint.Arb.Calc
, module Data.Number.Flint.Arb.FpWrap
-- * Complex
, module Data.Number.Flint.Acb
, module Data.Number.Flint.Acb.ComplexField
, module Data.Number.Flint.Acb.Acf
, module Data.Number.Flint.Acb.Poly
, module Data.Number.Flint.Acb.Mat
, module Data.Number.Flint.Acb.Hypgeom
, module Data.Number.Flint.Acb.Modular
, module Data.Number.Flint.Acb.Dirichlet
, module Data.Number.Flint.Acb.DFT
, module Data.Number.Flint.Acb.Calc
-- ** Exact real and complex numbers
, module Data.Number.Flint.Calcium
, module Data.Number.Flint.Calcium.Ca
, module Data.Number.Flint.Calcium.Ca.Poly
, module Data.Number.Flint.Calcium.Ca.Vec
, module Data.Number.Flint.Calcium.Ca.Mat
, module Data.Number.Flint.Calcium.Ca.Field
, module Data.Number.Flint.Calcium.Ca.Ext
, module Data.Number.Flint.Calcium.Fexpr
, module Data.Number.Flint.Calcium.Fexpr.Instances
, module Data.Number.Flint.Calcium.Fexpr.Builtin
-- ** Partitions
, module Data.Number.Flint.Partitions
-- ** Bernoulli numbers
, module Data.Number.Flint.Bernoulli
-- * Finite Fields
, module Data.Number.Flint.Fq
, module Data.Number.Flint.Fq.Embed
, module Data.Number.Flint.Fq.Poly
, module Data.Number.Flint.Fq.Poly.Factor
, module Data.Number.Flint.Fq.Vec
, module Data.Number.Flint.Fq.Mat
-- ** NMod
, module Data.Number.Flint.Fq.NMod
, module Data.Number.Flint.Fq.NMod.Embed
, module Data.Number.Flint.Fq.NMod.Poly
, module Data.Number.Flint.Fq.NMod.Poly.Factor
, module Data.Number.Flint.Fq.NMod.MPoly
, module Data.Number.Flint.Fq.NMod.MPoly.Factor
, module Data.Number.Flint.Fq.NMod.Mat
, module Data.Number.Flint.Fq.NMod.Vec
-- ** Zech
, module Data.Number.Flint.Fq.Zech
, module Data.Number.Flint.Fq.Zech.Embed
, module Data.Number.Flint.Fq.Zech.Poly
, module Data.Number.Flint.Fq.Zech.Poly.Factor
, module Data.Number.Flint.Fq.Zech.Vec
, module Data.Number.Flint.Fq.Zech.Mat
-- * p-adic Numbers
, module Data.Number.Flint.Padic
, module Data.Number.Flint.Padic.Poly
, module Data.Number.Flint.Padic.Mat
, module Data.Number.Flint.Qadic
-- * Floating-point support code
, module Data.Number.Flint.Support.ULong.Extras
, module Data.Number.Flint.Support.D.Extras
, module Data.Number.Flint.Support.D.Interval
, module Data.Number.Flint.Support.D.Mat
, module Data.Number.Flint.Support.D.Vec
, module Data.Number.Flint.Support.Mpf.Mat
, module Data.Number.Flint.Support.Mpf.Vec
, module Data.Number.Flint.Support.Mpfr.Mat
, module Data.Number.Flint.Support.Mpfr.Vec
) where

import Data.Number.Flint.Flint
import Data.Number.Flint.MPoly
-- Integers
import Data.Number.Flint.Fmpz
import Data.Number.Flint.Fmpz.Factor
import Data.Number.Flint.Fmpz.Arith
import Data.Number.Flint.Fmpz.Vec
import Data.Number.Flint.Fmpz.Mat
import Data.Number.Flint.Fmpz.Poly
import Data.Number.Flint.Fmpz.Poly.Mat
import Data.Number.Flint.Fmpz.Poly.Factor
import Data.Number.Flint.Fmpz.Poly.Q
import Data.Number.Flint.Fmpz.MPoly
import Data.Number.Flint.Fmpz.MPoly.Factor
import Data.Number.Flint.Fmpz.MPoly.Q
import Data.Number.Flint.Fmpz.LLL
import Data.Number.Flint.Fmpz.Mod
import Data.Number.Flint.Fmpz.Mod.Vec
import Data.Number.Flint.Fmpz.Mod.Mat
import Data.Number.Flint.Fmpz.Mod.Poly
import Data.Number.Flint.Fmpz.Mod.Poly.Factor
import Data.Number.Flint.Fmpz.Mod.MPoly
import Data.Number.Flint.Fmpz.Mod.MPoly.Factor
-- Rational numbers
import Data.Number.Flint.Fmpq
import Data.Number.Flint.Fmpq.Mat
import Data.Number.Flint.Fmpq.Vec
import Data.Number.Flint.Fmpq.Poly
import Data.Number.Flint.Fmpq.MPoly
import Data.Number.Flint.Fmpq.MPoly.Factor
-- APRCL primality testing
import Data.Number.Flint.APRCL
-- FFT
import Data.Number.Flint.FFT
-- import Data.Number.Flint.FFT.Small
-- Quadratic sieve
import Data.Number.Flint.QSieve
-- Integers mod n
import Data.Number.Flint.NMod
import Data.Number.Flint.NMod.Poly
import Data.Number.Flint.NMod.Poly.Factor
import Data.Number.Flint.NMod.Poly.Mat
import Data.Number.Flint.NMod.MPoly
import Data.Number.Flint.NMod.MPoly.Factor
import Data.Number.Flint.NMod.Mat
import Data.Number.Flint.NMod.Vec
-- Groups and other structures
import Data.Number.Flint.Groups.Perm
import Data.Number.Flint.Groups.Qfb
import Data.Number.Flint.Groups.Dirichlet
import Data.Number.Flint.Groups.DLog
import Data.Number.Flint.Groups.Bool.Mat
-- Number fields and algebraic structures
import Data.Number.Flint.NF
import Data.Number.Flint.NF.Elem
import Data.Number.Flint.NF.Fmpzi
import Data.Number.Flint.NF.QQbar
-- Finite fields
import Data.Number.Flint.Fq
import Data.Number.Flint.Fq.Embed
import Data.Number.Flint.Fq.Poly
import Data.Number.Flint.Fq.Poly.Factor
import Data.Number.Flint.Fq.Mat
import Data.Number.Flint.Fq.Vec
-- NMod
import Data.Number.Flint.Fq.NMod
import Data.Number.Flint.Fq.NMod.Embed
import Data.Number.Flint.Fq.NMod.Poly
import Data.Number.Flint.Fq.NMod.Poly.Factor
import Data.Number.Flint.Fq.NMod.MPoly
import Data.Number.Flint.Fq.NMod.MPoly.Factor
import Data.Number.Flint.Fq.NMod.Mat
import Data.Number.Flint.Fq.NMod.Vec
-- Zech
import Data.Number.Flint.Fq.Zech
import Data.Number.Flint.Fq.Zech.Embed
import Data.Number.Flint.Fq.Zech.Poly
import Data.Number.Flint.Fq.Zech.Poly.Factor
import Data.Number.Flint.Fq.Zech.Vec
import Data.Number.Flint.Fq.Zech.Mat
-- p-adic numbers
import Data.Number.Flint.Padic
import Data.Number.Flint.Padic.Poly
import Data.Number.Flint.Padic.Mat
import Data.Number.Flint.Qadic
-- Real and complex numbers
-- Real
import Data.Number.Flint.Arb
import Data.Number.Flint.Arb.Mag
import Data.Number.Flint.Arb.Arf
import Data.Number.Flint.Arb.Poly
import Data.Number.Flint.Arb.Fmpz.Poly
import Data.Number.Flint.Arb.Mat
import Data.Number.Flint.Arb.Hypgeom
import Data.Number.Flint.Arb.RealField
import Data.Number.Flint.Arb.Calc
import Data.Number.Flint.Arb.FpWrap
-- Complex
import Data.Number.Flint.Acb
import Data.Number.Flint.Acb.Acf
import Data.Number.Flint.Acb.Poly
import Data.Number.Flint.Acb.Mat
import Data.Number.Flint.Acb.Modular
import Data.Number.Flint.Acb.Dirichlet
import Data.Number.Flint.Acb.Hypgeom
import Data.Number.Flint.Acb.DFT
import Data.Number.Flint.Acb.ComplexField
import Data.Number.Flint.Acb.Calc
-- Exact real and complex numbers
import Data.Number.Flint.Calcium
import Data.Number.Flint.Calcium.Ca
import Data.Number.Flint.Calcium.Ca.Poly
import Data.Number.Flint.Calcium.Ca.Vec
import Data.Number.Flint.Calcium.Ca.Mat
import Data.Number.Flint.Calcium.Ca.Field
import Data.Number.Flint.Calcium.Ca.Ext
import Data.Number.Flint.Calcium.Fexpr
import Data.Number.Flint.Calcium.Fexpr.Builtin
-- Partitions
import Data.Number.Flint.Partitions
-- Bernoulli numbers
import Data.Number.Flint.Bernoulli
-- Floating-point support code
import Data.Number.Flint.Support.ULong.Extras
import Data.Number.Flint.Support.D.Extras
import Data.Number.Flint.Support.D.Interval
import Data.Number.Flint.Support.D.Mat
import Data.Number.Flint.Support.D.Vec
import Data.Number.Flint.Support.Mpf.Mat
import Data.Number.Flint.Support.Mpf.Vec
import Data.Number.Flint.Support.Mpfr.Mat
import Data.Number.Flint.Support.Mpfr.Vec

import Data.Number.Flint.UFD
import Data.Number.Flint.Quotient

import Data.Number.Flint.Fmpz.Instances
import Data.Number.Flint.Fmpz.Poly.Instances
import Data.Number.Flint.Fmpz.Poly.Q.Instances
import Data.Number.Flint.Fmpz.Mat.Instances

import Data.Number.Flint.Fmpq.Instances
import Data.Number.Flint.Fmpq.Poly.Instances
import Data.Number.Flint.Fmpq.Mat.Instances

import Data.Number.Flint.NF.Fmpzi.Instances
import Data.Number.Flint.NF.QQbar.Instances

import Data.Number.Flint.NMod.Poly.Instances

import Data.Number.Flint.Arb.Instances
import Data.Number.Flint.Arb.Mag.Instances
import Data.Number.Flint.Arb.Poly.Instances
import Data.Number.Flint.Arb.Mat.Instances

import Data.Number.Flint.Acb.Instances
import Data.Number.Flint.Acb.Poly.Instances
import Data.Number.Flint.Acb.Mat.Instances
import Data.Number.Flint.Acb.Modular.Instances

import Data.Number.Flint.Groups.Qfb.Instances
import Data.Number.Flint.Groups.Bool.Mat.Instances

import Data.Number.Flint.Support.D.Mat.Instances

import Data.Number.Flint.Calcium.Fexpr.Instances