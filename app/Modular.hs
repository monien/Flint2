module Modular where

import System.IO.Unsafe
import Foreign.Storable
import Data.Group
import Data.Ratio

import Data.Number.Flint hiding (numerator, denominator)

mediant l r = unsafePerformIO $ do
  result <- newFmpq
  withFmpq result $ \result -> do
    withFmpq r $ \r -> do
      withFmpq l $ \l -> do
        fmpq_mediant result r l
  return result

fareyNext [x, y] = x : mediant x y : [y]
fareyNext (x:y:xs) = x : mediant x y : fareyNext (y:xs)

fareyIter = iterate fareyNext [0, 1]
farey n = fareyIter !! n

fareyNext' [x, y] = x : mediant' x y : [y]
fareyNext' (x:y:xs) = x : mediant' x y : fareyNext' (y:xs)

fareyIter' = iterate fareyNext' [0, 1]
farey' n = fareyIter' !! n

mediant' x y = (numerator x + numerator y) % (denominator x + denominator y)

class Group' a b where
  action :: a -> b -> b

instance Group' PSL2Z Fmpq where
  action gamma z = unsafePerformIO $ do
    result <- newFmpq
    withPSL2Z gamma $ \gamma -> do
      CPSL2Z a b c d <- peek gamma
      withFmpq result $ \result -> do 
        withNewFmpz $ \p -> do
          withNewFmpz $ \q -> do
            withFmpq z $ \z -> do
              fmpq_get_fmpz_frac p q z
              withNewFmpz $ \tmp -> do
                withNewFmpz $ \num -> do
                  withNewFmpz $ \den -> do
                    fmpz_mul num a p
                    fmpz_mul tmp b q
                    fmpz_add num num tmp
                    fmpz_mul den c p
                    fmpz_mul tmp d q
                    fmpz_add den den tmp
                    fmpq_set_fmpz_frac result num den
    return result

rademacherMatrix :: Fmpq -> PSL2Z
rademacherMatrix x = unsafePerformIO $ do
  result <- newPSL2Z
  withPSL2Z result $ \result -> do
    CPSL2Z a b c d <- peek result
    withFmpq x $ \x -> do
      CFmpq h k <- peek x
      withNewFmpz $ \g -> do
        withNewFmpz $ \r -> do
          withNewFmpz $ \s -> do
            withNewFmpz $ \j -> do
              fmpz_xgcd g r s h k
              cmp <- fmpz_cmp_si r 0
              if cmp < 0 then do
                fmpz_set j r
                fmpz_neg j j
              else do
                fmpz_set j k
                fmpz_sub j j r
              fmpz_set a j
              fmpz_mul b h j
              fmpz_add_ui b b 1
              fmpz_neg b b
              fmpz_divexact b b k
              fmpz_set c k
              fmpz_set d h
              fmpz_neg d d
  return result

class Group a => WordProblem a where
  data Letter a
  hom :: Letter a -> a
  toWord :: a -> [(Letter a, Integer)]
  fromWord :: [(Letter a, Integer)] -> a
  fromWord w = mconcat $ map (\(x, n) -> hom x `pow` n) w

