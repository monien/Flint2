module Main where

import System.IO.Unsafe

import Foreign.Marshal (advancePtr)
import Foreign.Storable

import Test.QuickCheck
import Control.Monad

import Data.Number.Flint

import Fmpz
import FmpzFactor
import FmpzPoly
import Fmpq
import FmpqPoly

main = do
  x <- newFmpz
  withFmpz x $ \x -> do
    fmpz_set_ui x 7
    flag <- fmpz_print x
    endl
  let a = 15623679023253334147 :: Fmpz
      b = 13550662568090911171 :: Fmpz
      x = a * b
  print x
  print $ factor x
  withFmpz x $ \x ->
    withNewFmpzFactor $ \f -> do
      fmpz_factor f x
      fmpz_factor_print f
      endl
  r <- newFRandState
  replicateM_ 10 $ do
    withFRandState r $ \r -> do
      withFmpz x $ \x -> do
        fmpz_randbits x r 64
        putStr "random number: "
        fmpz_print x
        endl
        withNewFmpzFactor $ \f -> do
          fmpz_factor f x
          putStr "factorization: "
          fmpz_factor_print f
          endl
  l <- sample' arbitrary :: IO ([Fmpz])
  print l
  let n = 10
  v <- _fmpz_vec_init n
  forM_ [0..fromIntegral n-1] $ \j -> do
    fmpz_set_si (v `advancePtr` j) (fromIntegral (j+1)^2)
  _fmpz_vec_print v n
  f <- newFmpzFactor
  forM_ [0..fromIntegral n-1] $ \j -> do
    withFmpzFactor f $ \f -> do
      fmpz_factor f (v `advancePtr` j)
      fmpz_factor_print f
      endl
  _fmpz_vec_clear v n
  forM_ [0..10] $ \j ->
    print $ hermitePolynomial j
  let poly = product $ map hermitePolynomial [0..10]
  mapM_ print $ factor poly
  a <- newFmpzMat 3 3
  withFmpzMat a fmpz_mat_one
  withFmpzMat a fmpz_mat_print_pretty; endl
  withFmpzMat a $ \a -> do
    p <- fmpz_mat_entry a 0 2
    fmpz_set_ui p 7
  withFmpzMat a fmpz_mat_print_pretty; endl
  d <- newDMat 3 3
  withDMat d $ \d ->
    withFmpzMat a $ \a ->
      fmpz_mat_get_d_mat d a
  withDMat d $ \d ->
    forM_ [0..2] $ \i -> do
      forM_ [0..2] $ \j -> do
        x <- d_mat_get_entry d i j
        print $ x
  poly <- newFmpqPoly
  withFmpqPoly poly $ \poly -> do
    fmpq_poly_legendre_p poly 7
  print poly
  print $ poly^3
  testFmpqMat
  testPadic
  testPadicMat
  testQadic
  
endl = putStrLn ""

testPadic = do
  let p = 7 :: Fmpz
  withNewPadicCtx p 0 128 padic_series $ \ctx -> do
    withNewPadic $ \x -> do
      padic_set_ui x 2 ctx
      padic_print x ctx
      endl
      padic_sqrt x x ctx
      padic_print x ctx
      endl
      padic_neg x x ctx
      padic_print x ctx
      endl
      padic_mul x x x ctx
      padic_print x ctx
      endl
      v <- padic_get_val x
      print v
      prec <- padic_get_prec x
      print prec
      u <- padic_unit x
      fmpz_print u
      endl

testQadic = do
  let c = [1,10,9,8,8,0,2,9,1,3,1]
  p <- newFmpz
  withFmpz p $ \p -> fmpz_set_ui p 11
  withNewQadicCtx p 4 0 128 "a" padic_series $ \ctx -> do
    CQadicCtx pctx _ _ _ _ <- peek ctx
    withNewQadic $ \x -> do
      withFmpzPoly (fromList [3,0,4,8]) $ \poly -> do
        padic_poly_set_fmpz_poly x poly pctx
      newton x c ctx
      putStr "x = "
      qadic_print_pretty x ctx
      putStr "\n"
      y <- horner x c ctx
      withQadic y $ \y -> do
        putStr "y = "
        qadic_print_pretty y ctx
        putStr "\n"
         
newton x c ctx = do
  withNewQadic $ \y ->
    withNewQadic $ \y' -> do
      qadic_set_ui y (c!!0) ctx
      qadic_set_ui y' 0 ctx
      withNewQadic $ \tmp -> 
        forM_ (tail c) $ \c -> do
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
  withQadic y $ \y -> do
    qadic_set_ui y (c!!0) ctx
    withNewQadic $ \tmp ->
      forM_ (tail c) $ \c -> do
        qadic_mul y y x ctx
        qadic_set_ui tmp c ctx
        qadic_add y y tmp ctx
  return y

testPadicMat = do
  let p = 11 :: Fmpz
  withNewPadicCtx p 0 128 padic_terse $ \ctx -> do
    mat <- newPadicMat 3 3 20
    withPadicMat mat $ \mat -> do
      withNewFmpqMat 3 3 $ \r -> do
        fmpq_mat_hilbert_matrix r
        padic_mat_set_fmpq_mat mat r ctx
      padic_mat_print mat ctx
      endl
      padic_mat_print_pretty mat ctx
      endl

testFmpqMat = do
  mat <- newFmpqMat 3 3
  withFmpqMat mat $ \mat -> do
    fmpq_mat_one mat
    p <- fmpq_mat_entry mat 1 2
    fmpq_set_ui p 2 5
    fmpq_mat_print mat
    endl