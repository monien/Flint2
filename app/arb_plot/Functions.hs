module Functions where

import Control.Monad
import qualified Data.Map as Map
import Foreign.Ptr (Ptr, nullPtr)
import Foreign.C.Types (CLong)
import Data.Complex
import System.IO.Unsafe

import Data.Number.Flint.Arb
import Data.Number.Flint.Arb.Arf
import Data.Number.Flint.Arb.Hypgeom
import Data.Number.Flint.Acb
import Data.Number.Flint.Acb.Hypgeom
import Data.Number.Flint.Acb.Modular
import Data.Number.Flint.Acb.Elliptic

functions = Map.fromList
  [ ("gamma"     , gamma)
  , ("digamma"   , digamma)
  , ("lgamma"    , lgamma)
  , ("zeta"      , zeta)
  , ("erf"       , erf)
  , ("ai"        , ai)
  , ("bi"        , bi)
  , ("besselj"   , besselj)
  , ("bessely"   , bessely)
  , ("besseli"   , besseli)
  , ("besselk"   , besselk)
  , ("modj"      , modj)
  , ("modjq"     , modjq)
  , ("modeta"    , modeta)
  , ("modetaq"   , modetaq)
  , ("modlambda" , modlambda)
  , ("modlambdaq", modlambdaq)
  , ("ellipp"    , ellipp)
  , ("ellipzeta" , ellipzeta)
  , ("ellipsigma", ellipsigma)
  , ("barnesg"   , barnesg)
  , ("agm"       , agm)
  , ("fresnels"  , fresnels)
  , ("fresnelc"  , fresnelc)]

gamma   = acb_gamma
digamma = acb_digamma
lgamma  = acb_lgamma
zeta    = acb_zeta

agm = acb_agm1

ai res =
  acb_hypgeom_airy res
    (nullPtr :: Ptr CAcb)
    (nullPtr :: Ptr CAcb)
    (nullPtr :: Ptr CAcb)

bi res =
  acb_hypgeom_airy
    (nullPtr :: Ptr CAcb)
    (nullPtr :: Ptr CAcb)
    res
    (nullPtr :: Ptr CAcb)

barnesg   = acb_barnes_g

besselj res z prec = do 
  withNewAcb $ \nu -> acb_hypgeom_bessel_j res nu z prec
  return ()

bessely res z prec = do 
  withNewAcb $ \nu -> acb_hypgeom_bessel_y res nu z prec
  return ()

besseli res z prec = do 
  withNewAcb $ \nu -> acb_hypgeom_bessel_i res nu z prec
  return ()

besselk res z prec = do 
  withNewAcb $ \nu -> acb_hypgeom_bessel_k res nu z prec
  return ()

erf = acb_hypgeom_erf

modj res z prec = do
  acb_modular_j res z prec
  acb_div_ui res res 1728 prec

modjq res z prec = do
  withNewAcb $ \t -> do 
    acb_log res z prec
    acb_const_pi t prec
    acb_div res res t prec
    acb_mul_2exp_si res res (-1)
    acb_div_onei res res
    acb_modular_j res res prec
    acb_div_ui res res 1728 prec
  return ()
  
modeta = acb_modular_eta
modetaq res z prec = do
  withNewAcb $ \t -> do 
    acb_log res z prec
    acb_log res z prec
    acb_const_pi t prec
    acb_div res res t prec
    acb_mul_2exp_si res res (-1)
    acb_div_onei res res
    acb_modular_eta res res prec
  return ()
  
modlambda = acb_modular_lambda
modlambdaq res z prec = do
  withNewAcb $ \t -> do 
    acb_log res z prec
    acb_log res z prec
    acb_const_pi t prec
    acb_div res res t prec
    acb_mul_2exp_si res res (-1)
    acb_div_onei res res
    acb_modular_lambda res res prec
  return ()
  
ellipp res z prec = do
  acb_onei res
  acb_elliptic_p res z res prec

ellipzeta res z prec = do
  acb_onei res
  acb_elliptic_zeta res z res prec

ellipsigma res z prec = do
  acb_onei res
  acb_elliptic_sigma res z res prec

fresnels res z prec = acb_hypgeom_fresnel res (nullPtr :: Ptr CAcb) z 0 prec
fresnelc res z prec = acb_hypgeom_fresnel (nullPtr :: Ptr CAcb) res z 0 prec

eval zp prec (xa, xb, xnum) (ya, yb, ynum) f i j = do
    withNewArb $ \re -> do
      withNewArb $ \im -> do
        withNewArf $ \x -> do
          withNewArf $ \xap -> do
            withNewArf $ \xbp -> do
              withNewArf $ \y -> do
                withNewArf $ \yap -> do
                  withNewArf $ \ybp -> do
                    arf_set_d xap (realToFrac xa)
                    arf_set_d xbp (realToFrac xb)
                    arf_sub x xbp xap prec arf_rnd_down
                    arf_mul_ui x x (fromIntegral i) prec arf_rnd_down
                    arf_div_ui x x (fromIntegral xnum-1) prec arf_rnd_down
                    arf_add x x xap prec arf_rnd_down
                    arb_set_arf re x
                    arf_set_d yap (realToFrac ya)
                    arf_set_d ybp (realToFrac yb)
                    arf_sub y ybp yap prec arf_rnd_down
                    arf_mul_ui y y (fromIntegral j) prec arf_rnd_down
                    arf_div_ui y y (fromIntegral ynum-1) prec arf_rnd_down
                    arf_add y y yap prec arf_rnd_down
                    arb_set_arf im y
                    acb_set_arb_arb zp re im
                    f zp zp prec
    return ()

evalSafe (xa, xb, xnum) (ya, yb, ynum) f i j = unsafePerformIO $ do
  let iter prec = do
        (result, _) <- withNewAcb $ \value -> do
          eval value prec (xa, xb, xnum) (ya, yb, ynum) f i j
          finite <- acb_is_finite value
          bits <- acb_rel_accuracy_bits value
          when ((finite /= 1 || bits < 4) && prec < 500) $ do
            _ <- iter (prec + 30)
            return ()
          return value
        return result
      arb_get_d x = do
        m <- arb_midref x
        d <- arf_get_d m arf_rnd_near
        return d
  result <- iter 30
  (_, (_, (_, functionValue)))
    <- withAcb result $ \result -> do
      withNewArb $ \x -> do
        withNewArb $ \y-> do
          acb_get_real x result
          acb_get_imag y result
          dx <- arb_get_d x
          dy <- arb_get_d y
          return $ dx :+ dy
  return functionValue

    
  
    
