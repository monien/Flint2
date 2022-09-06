module Main where

import Test.QuickCheck
import Control.Monad

import Data.Number.Flint
import Fmpz

main = do
  x <- newFmpz
  withFmpz x $ \x -> do
    fmpz_set_ui x 7
    flag <- fmpz_print x
    putStrLn ""
  let a = 15623679023253334147 :: Fmpz
      b = 13550662568090911171 :: Fmpz
      x = a * b
  print x
  print $ factor x
  r <- newFRandState
  replicateM_ 10 $ do
    withFRandState r $ \r -> do
      withFmpz x $ \x -> do
        fmpz_randbits x r 64 
        fmpz_print x
        putStrLn ""
      print $ factor x
  l <- sample' arbitrary :: IO ([Fmpz])
  print l
    