
module Data.Number.Flint.Acb.ComplexField (
  CF(..)
, RF'(..)
, Special (..)
, realPart
, imagPart
-- * Polar form
, mkPolar
, cis
, polar
, magnitude
, phase
-- * Conjugate
, conjugate
) where

import GHC.TypeLits
import Data.Proxy
import Data.Ratio

import System.IO.Unsafe
import Control.Monad

import Foreign.C.String
import Foreign.C.Types
import Foreign.ForeignPtr
import Foreign.Ptr ( Ptr, FunPtr, castPtr )
import Foreign.Storable
import Foreign.Marshal ( free )
import Foreign.Marshal.Array ( advancePtr )

import Data.Number.Flint.Fmpz
import Data.Number.Flint.Fmpz.Instances
import Data.Number.Flint.Arb
import Data.Number.Flint.Arb.RealField

import Data.Number.Flint.Arb.Types
import Data.Number.Flint.Acb
import Data.Number.Flint.Acb.Acf
import Data.Number.Flint.Acb.Types
import Data.Number.Flint.Acb.Hypgeom
import Data.Number.Flint.Support.D.Interval

newtype CF (n :: Nat) = CF Acb

realPart :: forall n. KnownNat n => (CF n) -> (RF n)
realPart (CF z) = unsafePerformIO $ do
  res <- newArb
  withArb res $ \res -> do 
    withAcb z $ \z -> do
      acb_get_real res z
  return $ RF res

imagPart :: forall n. KnownNat n => (CF n) -> (RF n)
imagPart (CF z) = unsafePerformIO $ do
  res <- newArb
  withArb res $ \res -> do
    withAcb z $ \z -> do
      acb_get_imag res z
  return $ RF res

mkPolar :: forall n. KnownNat n => (RF n) -> (RF n) -> (CF n)
mkPolar (RF r) (RF theta) = unsafePerformIO $ do
  let prec = fromInteger $ natVal (Proxy :: Proxy n)
  res <- newAcb
  withAcb res $ \res -> do 
    withArb r $ \r -> do
      withArb theta $ \theta -> do
        withNewArb $ \x -> do
          withNewArb $ \y -> do
            arb_sin_cos y x theta prec
            arb_mul x x r prec
            arb_mul y y r prec
            acb_set_arb_arb res x y
  return $ CF res

cis :: forall n. KnownNat n => (RF n) -> (CF n)
cis (RF theta) = unsafePerformIO $ do
  let prec = fromInteger $ natVal (Proxy :: Proxy n)
  res <- newAcb
  withAcb res $ \res -> do 
    withArb theta $ \theta -> do
      withNewArb $ \x -> do
        withNewArb $ \y -> do
          arb_sin_cos y x theta prec
          acb_set_arb_arb res x y
  return $ CF res

polar :: forall n. KnownNat n => (CF n) -> (RF n, RF n)
polar z = (magnitude z, phase z)

magnitude :: forall n. KnownNat n => (CF n) -> (RF n)
magnitude (CF z) = unsafePerformIO $ do
  let prec = fromInteger $ natVal (Proxy :: Proxy n)
  res <- newArb
  withArb res $ \res -> do
    withAcb z $ \z -> do
      acb_abs res z prec
  return $ RF res

phase :: forall n. KnownNat n => (CF n) -> (RF n)
phase (CF z) = unsafePerformIO $ do
  let prec = fromInteger $ natVal (Proxy :: Proxy n)
  res <- newArb
  withArb res $ \res -> do
    withAcb z $ \z -> do
      acb_arg res z prec
  return $ RF res

conjugate :: forall n. KnownNat n => (CF n) -> (CF n)
conjugate (CF z) = unsafePerformIO $ do
  res <- newAcb
  withAcb res $ \res -> do
    withAcb z $ \z -> do
      acb_conj res z
  return $ CF res

instance forall n. KnownNat n => Eq (CF n) where
  {-# INLINE (==) #-}
  (==) = liftCmp acb_eq
  {-# INLINE (/=) #-}
  (/=) = liftCmp acb_ne

instance forall n. KnownNat n => Ord (CF n) where
  compare = undefined
  
instance forall n. KnownNat n => Num (CF n) where
  {-# INLINE (+) #-}
  (+) = lift2 acb_add
  {-# INLINE (-) #-}
  (-) = lift2 acb_sub
  {-# INLINE (*) #-}
  (*) = lift2 acb_mul
  {-# INLINE negate #-}
  negate = lift1 acb_neg
  abs = undefined
  {-# INLINE fromInteger #-}
  fromInteger x = unsafePerformIO $ do
    result <- newAcb
    let prec = fromInteger $ natVal (Proxy :: Proxy n)
    withAcb result $ \result -> do
      acb_set_ui result (fromIntegral x)
    return (CF result)
  signum = undefined
  
instance forall n. KnownNat n => Fractional (CF n) where
  {-# INLINE (/) #-}
  (/) = lift2 acb_div
  fromRational x = p / q where
    p = fromIntegral (numerator x) :: CF n
    q = fromIntegral (denominator x) :: CF n

instance forall n. KnownNat n => Real (CF n) where
  toRational = undefined
  
instance forall n. KnownNat n => RealFrac (CF n) where
  properFraction = undefined
  
instance forall n. KnownNat n => Floating (CF n) where
  pi = liftConstant arb_const_pi
  exp = liftF1 acb_exp
  log = liftF1 acb_log
  sqrt = liftF1 acb_sqrt
  sin = liftF1 acb_sin
  cos = liftF1 acb_cos
  tan = liftF1 acb_tan
  asin = liftF1 acb_asin
  acos = liftF1 acb_acos
  atan = liftF1 acb_atan
  sinh = liftF1 acb_sinh
  cosh = liftF1 acb_cosh
  tanh = liftF1 acb_tanh
  asinh = liftF1 acb_asinh
  acosh = liftF1 acb_acosh
  atanh = liftF1 acb_atanh
  
instance forall n. KnownNat n => Show (CF n) where
  show (CF x) = unsafePerformIO $ do
    let prec = fromInteger $ natVal (Proxy :: Proxy n)
        digits = floor (fromIntegral prec * logBase 10 2)
    (_, cstr) <- withAcb x $ \p ->
      acb_get_strn p (fromIntegral digits) arb_str_no_radius
    str <- peekCString cstr
    return str
    
------------------------------------------------------------------------

instance forall n. KnownNat n => Special (CF n) where
  gamma = liftF1 acb_gamma
  digamma = liftF1 acb_digamma
  lgamma = liftF1 acb_hypgeom_lgamma
  zeta = liftF1 acb_zeta
  erf = liftF1 acb_hypgeom_erf
  airy (CF x) = unsafePerformIO $ do
    let prec = fromInteger $ natVal (Proxy :: Proxy n)
    ai <- newAcb
    ai' <- newAcb
    bi <- newAcb
    bi' <- newAcb
    withAcb x $ \x -> 
      withAcb ai $ \ai -> 
        withAcb ai' $ \ai' ->
          withAcb bi $ \bi ->
            withAcb bi' $ \bi' ->
              acb_hypgeom_airy ai ai' bi bi' x prec
    return $ (CF ai, CF ai', CF bi, CF bi')
  airyZeros = undefined
  besselJ = lift2 acb_hypgeom_bessel_j
  besselY = lift2 acb_hypgeom_bessel_y
  besselI = lift2 acb_hypgeom_bessel_i
  besselK = lift2 acb_hypgeom_bessel_k
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
    
instance forall n. KnownNat n => RF' (CF n) where
  euler = liftConstant arb_const_euler
  glaisher = liftConstant arb_const_glaisher
  catalan = liftConstant arb_const_catalan
  khinchin = liftConstant arb_const_khinchin
  polylog = lift2 acb_polylog
  midPoint = lift1 acb_get_mid
  
-- lifting -------------------------------------------------------------

type Binary = Ptr CAcb -> Ptr CAcb -> Ptr CAcb -> CLong -> IO ()
type Cmp = Ptr CAcb -> Ptr CAcb -> IO CInt
type Function = Ptr CAcb -> Ptr CAcb -> IO ()

lift2 :: forall n. KnownNat n => Binary -> CF n -> CF n -> CF n
lift2 f (CF a) (CF b) = unsafePerformIO $ do
  let prec = fromInteger $ natVal (Proxy :: Proxy n)
  c <- newAcb
  withAcb a $ \a ->
    withAcb b $ \b ->
      withAcb c $ \c ->
        f c a b (CLong prec)
  return (CF c)

lift1 :: forall n. KnownNat n => Function -> CF n -> CF n
lift1 f (CF x) = unsafePerformIO $ do
  y <- newAcb
  withAcb x $ \x -> withAcb y $ \y -> f y x
  return (CF y)
  
lift0 f x = CF $ unsafePerformIO $ fst <$> withNewAcb (`f` x)
  
liftF1 :: forall n. KnownNat n =>
  (Ptr CAcb -> Ptr CAcb -> CLong -> IO ()) -> CF n -> CF n
liftF1 f (CF x) = unsafePerformIO $ do
  let prec = fromInteger $ natVal (Proxy :: Proxy n)
  y <- newAcb
  withAcb x $ \x -> withAcb y $ \y -> f y x (CLong prec)
  return (CF y)

liftCmp :: forall n. KnownNat n => Cmp -> CF n -> CF n -> Bool
liftCmp f (CF x) (CF y) = unsafePerformIO $ do
  (_, (_, cmp)) <- withAcb x $ \x -> withAcb y $ \y -> f x y
  return (cmp == 1)

liftProp :: forall n. KnownNat n => (Ptr CAcb -> IO CInt) -> CF n -> Bool
liftProp f (CF x)  = unsafePerformIO $ do
  (_, prop) <- withAcb x $ \x -> f x
  return (prop == 1)

liftConstant :: forall n. KnownNat n => (Ptr CArb -> CLong -> IO ()) -> CF n
liftConstant f = CF $ fst $ snd $ unsafePerformIO $ do
  let prec = fromInteger $ natVal (Proxy :: Proxy n)
  tmp <- newArb
  withArb tmp $ \tmp -> do
    f tmp prec
    withNewAcb (`acb_set_arb` tmp)

