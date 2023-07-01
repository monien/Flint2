{-# language 
  GADTs, 
  ScopedTypeVariables,
  DataKinds, 
  TypeFamilies, 
  TypeOperators 
  #-}

module Data.Number.Flint.Arb.RealField (
  RF(..),
  RF'(..),
  Special (..),
  ) where

import GHC.TypeLits
import Data.Proxy
import Data.Ratio

import System.IO.Unsafe
import Control.Monad

import Foreign.C.String
import Foreign.C.Types
import Foreign.ForeignPtr
import Foreign.Ptr ( Ptr, FunPtr )
import Foreign.Storable
import Foreign.Marshal (free)

import Data.Number.Flint.Arb
import Data.Number.Flint.Arb.Types

newtype RF (n :: Nat) = RF Arb

instance forall n. KnownNat n => Eq (RF n) where
  {-# INLINE (==) #-}
  (==) = liftCmp arb_eq
  {-# INLINE (/=) #-}
  (/=) = liftCmp arb_ne

instance forall n. KnownNat n => Ord (RF n) where
  {-# INLINE (<) #-}
  (<) = liftCmp arb_lt
  {-# INLINE (<=) #-}
  (<=) = liftCmp arb_le
  {-# INLINE (>) #-}
  (>) = liftCmp arb_gt
  {-# INLINE (>=) #-}
  (>=) = liftCmp arb_ge
  {-# INLINE max #-}
  max = lift2 arb_max
  {-# INLINE min #-}
  min = lift2 arb_min
  
instance forall n. KnownNat n => Num (RF n) where
  {-# INLINE (+) #-}
  (+) = lift2 arb_add
  {-# INLINE (-) #-}
  (-) = lift2 arb_sub
  {-# INLINE (*) #-}
  (*) = lift2 arb_mul
  {-# INLINE negate #-}
  negate = lift1 arb_neg
  {-# INLINE abs #-}
  abs = lift1 arb_abs
  {-# INLINE fromInteger #-}
  fromInteger x = unsafePerformIO $ do
    result <- newArb
    let prec = fromInteger $ natVal (Proxy :: Proxy n)
    withArb result $ \result -> do
      withCString (show x) $ \s -> do
        flag <- arb_set_str result s prec
        when (flag /= 0) $
          error $ "Could not create RF " ++ show prec ++ " from " ++ show x
    return (RF result)
  {-# INLINE signum #-}
  signum = lift1 arb_sgn
  
instance forall n. KnownNat n => Fractional (RF n) where
  {-# INLINE (/) #-}
  (/) = lift2 arb_div
  fromRational x = p / q where
    p = fromIntegral (numerator x) :: RF n
    q = fromIntegral (denominator x) :: RF n

instance forall n. KnownNat n => RealFloat (RF n) where
  isNaN = not . liftProp arb_is_finite
  isInfinite = not . liftProp arb_is_finite
  floatRadix _ = 2
  floatDigits _ = fromIntegral $ natVal (Proxy :: Proxy n)
  floatRange = error "floatRange: not defined"
  decodeFloat = error "decodeFloat: not defined"
  encodeFloat = error "encodeFloat: not defined"
  isDenormalized = error "isDenormalized: not defined"
  isNegativeZero = error "isNegativeZero: not defined"
  isIEEE _ = False
  atan2 = lift2 arb_atan2

instance forall n. KnownNat n => Real (RF n) where
  toRational = error "toRational: not defined"
  
instance forall n. KnownNat n => RealFrac (RF n) where
  properFraction = error "properFraction: not defined."
  
instance forall n. KnownNat n => Floating (RF n) where
  pi = liftConstant arb_const_pi
  exp = liftF1 arb_exp
  log = liftF1 arb_log
  sqrt = liftF1 arb_sqrt
  sin = liftF1 arb_sin
  cos = liftF1 arb_cos
  tan = liftF1 arb_tan
  asin = liftF1 arb_asin
  acos = liftF1 arb_acos
  atan = liftF1 arb_atan
  sinh = liftF1 arb_sinh
  cosh = liftF1 arb_cosh
  tanh = liftF1 arb_tanh
  asinh = liftF1 arb_asinh
  acosh = liftF1 arb_acosh
  atanh = liftF1 arb_atanh
  
instance forall n. KnownNat n => Show (RF n) where
  show (RF x) = unsafePerformIO $ do
    let prec = fromInteger $ natVal (Proxy :: Proxy n)
        digits = floor (fromIntegral prec * logBase 10 2)
    (_, cstr) <- withArb x $ \p ->
      arb_get_str p (fromIntegral digits) arb_str_no_radius
    str <- peekCString cstr
    return str

------------------------------------------------------------------------

instance forall n. KnownNat n => Special (RF n) where
  gamma = liftF1 arb_gamma
  digamma = liftF1 arb_digamma
  lgamma = undefined
  zeta = undefined
  erf = undefined
  ai = undefined
  bi = undefined
  besselj = undefined
  bessely = undefined
  besseli = undefined
  besselk = undefined
  modj = undefined
  modjq = undefined
  modeta = undefined
  modetaq = undefined
  modlambda = undefined
  modlambdaq = undefined
  ellipp = undefined
  ellipzeta = undefined
  ellipsigma = undefined
  barnesg = undefined
  agm = undefined
  fresnels = undefined
  fresnelc = undefined
  
class RF' a where
  euler :: a
  glaisher :: a
  catalan :: a
  khinchin :: a
  polylog :: a -> a -> a
  midPoint :: a -> a
  
instance forall n. KnownNat n => RF' (RF n) where
  euler = liftConstant arb_const_euler
  glaisher = liftConstant arb_const_glaisher
  catalan = liftConstant arb_const_catalan
  khinchin = liftConstant arb_const_khinchin
  polylog = lift2 arb_polylog
  midPoint = lift1 arb_get_mid_arb

-- toDouble :: forall n. KnownNat n => RF n -> Double
-- toDouble (RF x) = snd $ unsafePerformIO $ 
--   withArb x $ \x -> do
--     d <- arf_get_d (arb_midref x) arf_rnd_down
--     return $ realToFrac d
    
-- lifting -------------------------------------------------------------

type Binary = Ptr CArb -> Ptr CArb -> Ptr CArb -> CLong -> IO ()
type Cmp = Ptr CArb -> Ptr CArb -> IO CInt
type Function = Ptr CArb -> Ptr CArb -> IO ()

lift2 :: forall n. KnownNat n => Binary -> RF n -> RF n -> RF n
lift2 f (RF a) (RF b) = unsafePerformIO $ do
  let prec = fromInteger $ natVal (Proxy :: Proxy n)
  c <- newArb
  withArb a $ \a ->
    withArb b $ \b ->
      withArb c $ \c ->
        f c a b (CLong prec)
  return (RF c)

lift1 :: forall n. KnownNat n => Function -> RF n -> RF n
lift1 f (RF x) = unsafePerformIO $ do
  y <- newArb
  withArb x $ \x -> withArb y $ \y -> f y x
  return (RF y)
  
lift0 f x = RF $ unsafePerformIO $ fst <$> withNewArb (`f` x)
  
liftF1 :: forall n. KnownNat n =>
  (Ptr CArb -> Ptr CArb -> CLong -> IO ()) -> RF n -> RF n
liftF1 f (RF x) = unsafePerformIO $ do
  let prec = fromInteger $ natVal (Proxy :: Proxy n)
  y <- newArb
  withArb x $ \x -> withArb y $ \y -> f y x (CLong prec)
  return (RF y)

liftCmp :: forall n. KnownNat n => Cmp -> RF n -> RF n -> Bool
liftCmp f (RF x) (RF y) = unsafePerformIO $ do
  (_, (_, cmp)) <- withArb x $ \x -> withArb y $ \y -> f x y
  return (cmp == 1)

liftProp :: forall n. KnownNat n => (Ptr CArb -> IO CInt) -> RF n -> Bool
liftProp f (RF x)  = unsafePerformIO $ do
  (_, prop) <- withArb x $ \x -> f x
  return (prop == 1)

liftConstant :: forall n. KnownNat n => (Ptr CArb -> CLong -> IO ()) -> RF n
liftConstant f = RF $ unsafePerformIO $ do
  let prec = fromInteger $ natVal (Proxy :: Proxy n)
  fst <$> withNewArb (`f` CLong prec)

class Special a where
  gamma :: a -> a
  digamma :: a -> a
  lgamma :: a -> a
  zeta :: a -> a
  erf :: a -> a
  ai :: a -> a
  bi :: a -> a
  besselj :: a -> a
  bessely :: a -> a
  besseli :: a -> a
  besselk :: a -> a
  modj :: a -> a
  modjq :: a -> a
  modeta :: a -> a
  modetaq :: a -> a
  modlambda :: a -> a
  modlambdaq :: a -> a
  ellipp :: a -> a
  ellipzeta :: a -> a
  ellipsigma :: a -> a
  barnesg :: a -> a
  agm :: a -> a
  fresnels :: a -> a
  fresnelc :: a -> a
