{-|
module      :  Data.Number.Flint.Fq.Embed.FFI
copyright   :  (c) 2022 Hartmut Monien
license     :  GNU GPL, version 2 or above (see LICENSE)
maintainer  :  hmonien@uni-bonn.de
-}
module Data.Number.Flint.Fq.Embed.FFI (
  -- * Computing isomorphisms and embeddings of finite fields
    fq_embed_gens
  , _fq_embed_gens_naive
  , fq_embed_matrices
  , fq_embed_trace_matrix
  , fq_embed_composition_matrix
  , fq_embed_composition_matrix_sub
  , fq_embed_mul_matrix
  , fq_embed_mono_to_dual_matrix
  , fq_embed_dual_to_mono_matrix
  , fq_modulus_pow_series_inv
  , fq_modulus_derivative_inv
) where

import Foreign.Ptr
import Foreign.C.Types

import Data.Number.Flint.Fmpz.Mod.Poly
import Data.Number.Flint.Fmpz.Mod.Mat

import Data.Number.Flint.Fq

-- Computing isomorphisms and embeddings of finite fields ----------------------

-- | /fq_embed_gens/ /gen_sub/ /gen_sup/ /minpoly/ /sub_ctx/ /sup_ctx/ 
--
-- Given two contexts @sub_ctx@ and @sup_ctx@, such that @degree(sub_ctx)@
-- divides @degree(sup_ctx)@, compute:
-- 
-- -   an element @gen_sub@ in @sub_ctx@ such that @gen_sub@ generates the
--     finite field defined by @sub_ctx@,
-- -   its minimal polynomial @minpoly@,
-- -   a root @gen_sup@ of @minpoly@ inside the field defined by @sup_ctx@.
-- 
-- These data uniquely define an embedding of @sub_ctx@ into @sup_ctx@.
foreign import ccall "fq_embed.h fq_embed_gens"
  fq_embed_gens :: Ptr CFq -> Ptr CFq -> Ptr CFmpzModPoly -> Ptr CFqCtx -> Ptr CFqCtx -> IO ()

-- | /_fq_embed_gens_naive/ /gen_sub/ /gen_sup/ /minpoly/ /sub_ctx/ /sup_ctx/ 
--
-- Given two contexts @sub_ctx@ and @sup_ctx@, such that @degree(sub_ctx)@
-- divides @degree(sup_ctx)@, compute an embedding of @sub_ctx@ into
-- @sup_ctx@ defined as follows:
-- 
-- -   @gen_sub@ is the canonical generator of @sup_ctx@ (i.e., the class
--     of \(X\)),
-- -   @minpoly@ is the defining polynomial of @sub_ctx@,
-- -   @gen_sup@ is a root of @minpoly@ inside the field defined by
--     @sup_ctx@.
foreign import ccall "fq_embed.h _fq_embed_gens_naive"
  _fq_embed_gens_naive :: Ptr CFq -> Ptr CFq -> Ptr CFmpzModPoly -> Ptr CFqCtx -> Ptr CFqCtx -> IO ()

-- | /fq_embed_matrices/ /embed/ /project/ /gen_sub/ /sub_ctx/ /gen_sup/ /sup_ctx/ /gen_minpoly/ 
--
-- Given:
-- 
-- -   two contexts @sub_ctx@ and @sup_ctx@, of respective degrees \(m\)
--     and \(n\), such that \(m\) divides \(n\);
-- -   a generator @gen_sub@ of @sub_ctx@, its minimal polynomial
--     @gen_minpoly@, and a root @gen_sup@ of @gen_minpoly@ in @sup_ctx@,
--     as returned by @fq_embed_gens@;
-- 
-- Compute:
-- 
-- -   the \(n\times m\) matrix @embed@ mapping @gen_sub@ to @gen_sup@, and
--     all their powers accordingly;
-- -   an \(m\times n\) matrix @project@ such that @project@ \(\times\)
--     @embed@ is the \(m\times m\) identity matrix.
foreign import ccall "fq_embed.h fq_embed_matrices"
  fq_embed_matrices :: Ptr CFmpzModMat -> Ptr CFmpzModMat -> Ptr CFq -> Ptr CFqCtx -> Ptr CFq -> Ptr CFqCtx -> Ptr CFmpzModPoly -> IO ()

-- | /fq_embed_trace_matrix/ /res/ /basis/ /sub_ctx/ /sup_ctx/ 
--
-- Given:
-- 
-- -   two contexts @sub_ctx@ and @sup_ctx@, of degrees \(m\) and \(n\),
--     such that \(m\) divides \(n\);
-- -   an \(n\times m\) matrix @basis@ that maps @sub_ctx@ to an isomorphic
--     subfield in @sup_ctx@;
-- 
-- Compute the \(m\times n\) matrix of the trace from @sup_ctx@ to
-- @sub_ctx@.
-- 
-- This matrix is computed as
-- 
-- @embed_dual_to_mono_matrix(_, sub_ctx)@ \(\times\) @basis@t \(\times\)
-- @embed_mono_to_dual_matrix(_, sup_ctx)@.
-- 
-- __Note:__ if \(m=n\), @basis@ represents a Frobenius, and the result is
-- its inverse matrix.
foreign import ccall "fq_embed.h fq_embed_trace_matrix"
  fq_embed_trace_matrix :: Ptr CFmpzModMat -> Ptr CFmpzModMat -> Ptr CFqCtx -> Ptr CFqCtx -> IO ()

-- | /fq_embed_composition_matrix/ /matrix/ /gen/ /ctx/ 
--
-- Compute the /composition matrix/ of @gen@.
-- 
-- For an element \(a\in\mathbf{F}_{p^n}\), its composition matrix is the
-- matrix whose columns are \(a^0, a^1, \ldots, a^{n-1}\).
foreign import ccall "fq_embed.h fq_embed_composition_matrix"
  fq_embed_composition_matrix :: Ptr CFmpzModMat -> Ptr CFq -> Ptr CFqCtx -> IO ()

-- | /fq_embed_composition_matrix_sub/ /matrix/ /gen/ /ctx/ /trunc/ 
--
-- Compute the /composition matrix/ of @gen@, truncated to @trunc@ columns.
foreign import ccall "fq_embed.h fq_embed_composition_matrix_sub"
  fq_embed_composition_matrix_sub :: Ptr CFmpzModMat -> Ptr CFq -> Ptr CFqCtx -> CLong -> IO ()

-- | /fq_embed_mul_matrix/ /matrix/ /gen/ /ctx/ 
--
-- Compute the /multiplication matrix/ of @gen@.
-- 
-- For an element \(a\) in \(\mathbf{F}_{p^n}=\mathbf{F}_p[x]\), its
-- multiplication matrix is the matrix whose columns are \(a, ax,
-- \dots, ax^{n-1}\).
foreign import ccall "fq_embed.h fq_embed_mul_matrix"
  fq_embed_mul_matrix :: Ptr CFmpzModMat -> Ptr CFq -> Ptr CFqCtx -> IO ()

-- | /fq_embed_mono_to_dual_matrix/ /res/ /ctx/ 
--
-- Compute the change of basis matrix from the monomial basis of @ctx@ to
-- its dual basis.
foreign import ccall "fq_embed.h fq_embed_mono_to_dual_matrix"
  fq_embed_mono_to_dual_matrix :: Ptr CFmpzModMat -> Ptr CFqCtx -> IO ()

-- | /fq_embed_dual_to_mono_matrix/ /res/ /ctx/ 
--
-- Compute the change of basis matrix from the dual basis of @ctx@ to its
-- monomial basis.
foreign import ccall "fq_embed.h fq_embed_dual_to_mono_matrix"
  fq_embed_dual_to_mono_matrix :: Ptr CFmpzModMat -> Ptr CFqCtx -> IO ()

-- | /fq_modulus_pow_series_inv/ /res/ /ctx/ /trunc/ 
--
-- Compute the power series inverse of the reverse of the modulus of @ctx@
-- up to \(O(x^\texttt{trunc})\).
foreign import ccall "fq_embed.h fq_modulus_pow_series_inv"
  fq_modulus_pow_series_inv :: Ptr CFmpzModPoly -> Ptr CFqCtx -> CLong -> IO ()

-- | /fq_modulus_derivative_inv/ /m_prime/ /m_prime_inv/ /ctx/ 
--
-- Compute the derivative @m_prime@ of the modulus of @ctx@ as an element
-- of @ctx@, and its inverse @m_prime_inv@.
foreign import ccall "fq_embed.h fq_modulus_derivative_inv"
  fq_modulus_derivative_inv :: Ptr CFq -> Ptr CFq -> Ptr CFqCtx -> IO ()

