{- |
module      :  Data.Number.Flint.Fq
copyright   :  (c) 2023 Hartmut Monien
license     :  BSD-style (see LICENSE)
maintainer  :  hmonien@uni-bonn.de

= Finite fields

This module implements operations over the finite field \(\mathbb F_q\) where \( q = p^d \) with \(p\) prime.

== Basic usage

Consider the finite field \(\mathbb F_{11^4}\). Here we initialize the
context and set @x@ to the generator of the field and print it and its
fourth power.

@
import Data.Number.Flint

main = do
  ctx <- newFqCtx 11 4 "alpha"
  withNewFq ctx $ \\x -> do 
    withFqCtx ctx $ \\ctx -> do
      fq_ctx_print ctx
      putStr "\\n"
      fq_gen x ctx
      fq_print_pretty x ctx
      putStr "\\n"
      fq_pow_ui x x 4 ctx
      fq_print_pretty x ctx
      putStr "\\n"
@

Running main yields:

>>> main 
p = 11
d = 4
f(X) = X^4+8*X^2+10*X+2
<BLANKLINE>
alpha 
3*alpha^2+alpha+9
-}
module Data.Number.Flint.Fq (
  module Data.Number.Flint.Fq.FFI
) where

import Data.Number.Flint.Fq.FFI
  
