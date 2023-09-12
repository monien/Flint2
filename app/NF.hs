{-# language DataKinds #-}

module NF (
  NumberField (..)
, polynomial
, generator
, nf_get_ctx
) where

import GHC.TypeLits
import System.IO.Unsafe

import Foreign.C.String
import Foreign.C.Types
import Foreign.Marshal.Alloc

import Data.Proxy
import Data.Ratio

import Data.Number.Flint hiding (numerator, denominator)

data NumberField (s :: Symbol) = Element NFElem

instance forall s . KnownSymbol s => Show (NumberField s) where
  show x@(Element e) =  snd $ snd $ unsafePerformIO $ do
    nf <- nf_get_ctx x
    withNF nf $ \nf -> do
      withNFElem e $ \e -> do
        withCString "a" $ \a -> do
          cs <- nf_elem_get_str_pretty e a nf
          s <- peekCString cs
          free cs
          return s
          
instance forall s . KnownSymbol s => Num (NumberField s) where
  fromInteger x = unsafePerformIO $ do  
    let poly = fromList [fromInteger x] :: FmpqPoly
    nf <- nf_get_ctx (undefined :: NumberField s)
    e <- newNFElem nf
    withFmpqPoly poly $ \poly -> do
      withNF nf $ \nf -> do
        withNFElem e $ \e -> do
          nf_elem_set_fmpq_poly e poly nf
    return $ Element e
  (+) = lift2 nf_elem_add
  (-) = lift2 nf_elem_sub
  (*) = lift2 nf_elem_mul
  abs = undefined
  signum = undefined

instance forall s . KnownSymbol s => Fractional (NumberField s) where
  (/) = lift2 nf_elem_div
  fromRational x = fromInteger (numerator x) / fromInteger (denominator x)
  
lift2 :: forall s . KnownSymbol s =>
  (Ptr CNFElem -> Ptr CNFElem -> Ptr CNFElem -> Ptr CNF -> IO ()) ->
  NumberField s -> NumberField s -> NumberField s 
lift2 f (Element x) (Element y) = unsafePerformIO $ do
  nf <- nf_get_ctx (undefined :: NumberField s)
  result <- newNFElem nf
  withNF nf $ \nf -> do
    withNFElem x $ \x -> do
      withNFElem y $ \y -> do
        withNFElem result $ \result -> do
          f result x y nf
  return $ Element result
  
nf_get_ctx :: forall s . KnownSymbol s => NumberField s -> IO NF
nf_get_ctx _ =  do
  putStrLn "nf_get_ctx"
  poly <- newFmpqPoly
  let s = symbolVal (Proxy :: Proxy s)
  withCString s $ \cs ->
    withFmpqPoly poly $ \poly -> do 
      fmpq_poly_set_str poly cs
  newNF poly
  
polynomial :: forall s . KnownSymbol s => NumberField s -> IO FmpqPoly
polynomial _ = do
  poly <- newFmpqPoly
  let s = symbolVal (Proxy :: Proxy s)
  withCString s $ \cs ->
    withFmpqPoly poly $ \poly -> do 
      fmpq_poly_set_str poly cs
  return poly

generator :: forall s t . KnownSymbol s => IO (NumberField s)
generator = do
  poly <- polynomial (undefined :: NumberField s)
  nf <- newNF poly
  e <- newNFElem nf
  withNF nf $ \nf -> do
    withNFElem e $ \e -> do
      nf_elem_one e nf
      nf_elem_mul_gen e e nf
  return $ Element e