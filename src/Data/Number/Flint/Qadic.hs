{-|
module      :  Data.Number.Flint.Qadic
copyright   :  (c) 2022 Hartmut Monien
license     :  GNU GPL, version 2 or above (see LICENSE)
maintainer  :  hmonien@uni-bonn.de

= Unramified extensions over p-adic numbers

A @Qadic@ represents an element 
of \(\mathbb{Q}_q \cong \mathbb{Q}_p[X] / (f(X))\). 
This module implements operations on q-adic numbers.

== Example

Calculate a root of the 
polynomial \(x^{10}+10x^9+9x^8+8x^7+8x^6+2x^4+9x^3+x^2+3x+1\)
over \(K=\mathbb{Q}_{{11}^4} \cong \mathbb{Q}_{11}[X] /(X^4+8X^2+10X+2)\) to
standard padic precision using 
Newton iteration. The iteration starts with \(x=8a^3+4a^2+3\) where \(a\)
is a generator of \(K\). The value of \(x\) is initialized using a `FmpzPoly`.

@ 
import Data.Number.Flint

main = do
  let c = [1,10,9,8,8,0,2,9,1,3,1]
  withNewQadicCtx 11 4 0 128 "a" padic_series $ \\ctx -> do
    CQadicCtx pctx _ _ _ _ <- peek ctx
    withNewQadic $ \\x -> do
      withFmpzPoly (fromList [3,0,4,8]) $ \\poly -> do
        padic_poly_set_fmpz_poly x poly pctx
      newton x c ctx
      putStr "x = "
      qadic_print_pretty x ctx
      putStr "\\n"
      y <- horner x c ctx
      withQadic y $ \\y -> do
        putStr "y = "
        qadic_print_pretty y ctx
        putStr "\\n"
         
newton x c ctx = do
  withNewQadic $ \\y ->
    withNewQadic $ \\y' -> do
      qadic_set_ui y (c!!0) ctx
      qadic_set_ui y' 0 ctx
      withNewQadic $ \\tmp -> 
        forM_ (tail c) $ \\c -> do
          qadic_set_ui tmp c ctx
          qadic_mul y' y' x ctx
          qadic_add y' y' y ctx
          qadic_mul y y x ctx
          qadic_add y y tmp ctx
      is_zero <- qadic_is_zero y
      qadic_inv y' y' ctx
      qadic_mul y y y' ctx
      qadic_sub x x y ctx
      when (is_zero /= 1) $ newton x c ctx
  return ()

horner x c ctx = do
  y <- newQadic
  withQadic y $ \\y -> do
    qadic_set_ui y (head c) ctx
    withNewQadic $ \\tmp ->
      forM_ (tail c) $ \\c -> do
        qadic_mul y y x ctx
        qadic_set_ui tmp c ctx
        qadic_add y y tmp ctx
  return y

@

Running main yields:

>>> main 
x = (8*a^3+4*a^2+3) + (8*a^2+2*a+5)*11 + (8*a^3+a^2+6)*11^2 + (7*a^3+6*a^2+2*a+6)*11^3 + (10*a^3+6*a^2+9*a+3)*11^4 + (6*a^3+6*a^2+3*a+7)*11^5 + (7*a^3+5*a^2+9*a+9)*11^6 + (2*a^2+4*a+3)*11^7 + (a^3+3*a^2+3*a+8)*11^8 + (2*a^3+2*a^2+8*a+2)*11^9 + (5*a^3+9*a^2)*11^10 + (2*a^3+3*a^2+2*a+7)*11^11 + (a^3+4*a^2+7*a+3)*11^12 + (10*a^3+9*a^2+10*a+6)*11^13 + (7*a^3+a^2+9*a+3)*11^14 + (10*a^3+10*a^2+6*a+4)*11^15 + (3*a^3+a^2+2*a+1)*11^16 + (4*a^3+6*a^2+8*a)*11^17 + (2*a^3+9*a^2+9*a+10)*11^18 + (4*a^3+4*a^2+5*a+4)*11^19
-}

module Data.Number.Flint.Qadic (
  module Data.Number.Flint.Qadic.FFI,
) where

import Data.Number.Flint.Qadic.FFI

