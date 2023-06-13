{-# language 
  GADTs
, ScopedTypeVariables
, DataKinds
, TypeFamilies
, TypeOperators
, KindSignatures #-}
module RF(
  -- * Real field with n binary digits.
  RF (..),
) where

import GHC.TypeLits

import Data.Proxy
import Data.Ratio
import Data.Char (toLower)
import Data.Maybe (fromMaybe)

import Text.Printf

import Foreign.C.Types
import Foreign.C.String
import Foreign.Ptr
import Foreign.Marshal.Alloc (free)

import System.IO.Unsafe

import GHC.Read 
import qualified Text.Read.Lex as Lex
import Text.ParserCombinators.ReadPrec hiding (prec)

import Data.Number.Flint.Arb
import Data.Number.Flint.Arb.Types

newtype RF (n :: Nat) = RF Arb

instance forall n. KnownNat n => Eq (RF n) where
  (RF x) == (RF y) = unsafePerformIO $ do
    (_,(_,result)) <- withArb x $ \x -> do
      withArb y $ \y -> do
        u <- arb_is_exact x
        v <- arb_is_exact y
        return $ if u == 1 && v == 1 then True else False
    return result
    
instance forall n. KnownNat n => Ord (RF n) where
  compare (RF x) (RF y) = unsafePerformIO $ do
    (_,(_,result)) <- withArb x $ \x -> do
      withArb y $ \y -> do 
        lt <- arb_lt x y
        gt <- arb_gt x y
        return $ if lt == 1
                   then LT
                   else if gt == 1 then GT else EQ
    return result

instance forall n. KnownNat n => Num (RF n) where
  (*) = lift2 arb_mul
  (+) = lift2 arb_add
  (-) = lift2 arb_sub
  abs = lift1' arb_abs
  signum = lift1' arb_sgn
  fromInteger n = unsafePerformIO $ do
    x <- newArb
    withArb x $ \x -> arb_set_si x (fromIntegral n)
    return $ RF x

instance forall n. KnownNat n => Fractional (RF n) where
  (/) = lift2 arb_div
  fromRational x = p/q where
    prec = fromInteger $ natVal (Proxy :: Proxy n)
    p = fromInteger (numerator x) :: RF n
    q = fromInteger (denominator x) :: RF n
    
instance forall n. KnownNat n => Floating (RF n) where
  pi = liftConstant arb_const_pi
  exp = lift1 arb_exp
  sqrt = lift1 arb_sqrt
  log = lift1 arb_log
  sin = lift1 arb_sin
  cos = lift1 arb_cos
  tan = lift1 arb_tan
  sinh = lift1 arb_sinh
  cosh = lift1 arb_cosh
  tanh = lift1 arb_tanh
  asin = lift1 arb_asin
  acos = lift1 arb_acos
  atan = lift1 arb_atan
  asinh = lift1 arb_asinh
  acosh = lift1 arb_acosh
  atanh = lift1 arb_atanh
  
instance forall n. KnownNat n => Show (RF n) where
  show (RF x) = snd $ unsafePerformIO $ do
    let bit_prec = fromInteger $ natVal (Proxy :: Proxy n)
        prec = floor (bit_prec * logBase 10 2)
    withArb x $ \x -> do
      cs <- arb_get_str x prec arb_str_no_radius
      s <- peekCString cs
      free cs
      return s

instance forall n. KnownNat n => Real (RF n) where
  toRational (RF x) = undefined

instance forall n. KnownNat n => Read (RF n) where
  readPrec     = readNumber convertFrac
  readListPrec = readListPrecDefault
  readList     = readListDefault

instance forall n. KnownNat n => RealFrac (RF n) where
  properFraction x = (d, f) where
    prec = fromInteger $ natVal (Proxy :: Proxy n)
    r = toRational x
    (p, q) = (numerator r, denominator r)
    d = fromInteger (div p q)
    f = fromRational (r - toRational d)

instance forall n. KnownNat n => RealFloat (RF n) where
  floatRadix (RF x) = 2
  floatDigits (RF x) = fromIntegral prec where
    prec = fromInteger $ natVal (Proxy :: Proxy n) 
  -- need to check ------------------------------------------------------
  floatRange (RF x) = getBounds
  decodeFloat (RF x) = undefined
  encodeFloat a e = undefined
  isNaN (RF x) = undefined
  isInfinite (RF x) = undefined
  isIEEE _ = False
  isDenormalized _ = False
  isNegativeZero _ = False
  atan2 = undefined

getBounds = undefined

convertFrac :: RealFloat a => Lex.Lexeme -> ReadPrec a
convertFrac (Lex.Ident "NaN")      = return (0 / 0)
convertFrac (Lex.Ident "Infinity") = return (1 / 0)
convertFrac (Lex.Number n) = let resRange = floatRange (undefined :: a)
                           in case Lex.numberToRangedRational resRange n of
                              Nothing -> return (1 / 0)
                              Just rat -> return $ fromRational rat
convertFrac _            = pfail

lift1 :: forall n. KnownNat n =>
  (Ptr CArb -> Ptr CArb -> CLong -> IO ()) ->
  (RF n -> RF n)
lift1 f (RF x) = unsafePerformIO $ do
  let prec = fromInteger $ natVal (Proxy :: Proxy n) 
  result <- newArb
  withArb result $ \result -> do
    withArb x $ \x -> do
      f result x prec
  return $ RF result

lift1' :: forall n. KnownNat n =>
  (Ptr CArb -> Ptr CArb -> IO ()) ->
  (RF n -> RF n)
lift1' f (RF x) = unsafePerformIO $ do
  let prec = fromInteger $ natVal (Proxy :: Proxy n) 
  result <- newArb
  withArb result $ \result -> do
    withArb x $ \x -> do
      f result x
      arb_get_mid_arb result result
  return $ RF result
  
lift2 :: forall n. KnownNat n =>
  (Ptr CArb -> Ptr CArb -> Ptr CArb -> CLong -> IO ()) ->
  (RF n -> RF n -> RF n)
lift2 f (RF x) (RF y) = unsafePerformIO $ do
  let prec = fromInteger $ natVal (Proxy :: Proxy n) 
  result <- newArb
  withArb result $ \result -> do
    withArb x $ \x -> do
      withArb y $ \y-> do
        f result x y prec
        arb_get_mid_arb result result
  return $ RF result

liftConstant :: forall n. KnownNat n =>
  (Ptr CArb -> CLong -> IO ()) -> RF n
liftConstant f = unsafePerformIO $ do
  let prec = fromInteger $ natVal (Proxy :: Proxy n) 
  result <- newArb
  withArb result $ \result -> do
    f result prec
  return $ RF result