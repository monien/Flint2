import Data.List (intercalate)
import qualified Data.Map as Map

import Data.Complex

import System.IO
import System.IO.Unsafe

import Options.Applicative

import Codec.Picture
import Graphics.Gloss 
import Graphics.Gloss.Juicy

import ColorFunction
import Functions

main = run =<< execParser opts where
  opts = info (parameters <**> helper) (
       fullDesc
    <> progDesc "\nplotting special functions:\n"
    <> header "test program for arb.")

run p@(Parameters xa xb ya yb w h colorMode f) = do
  case Map.lookup f functions of 
    Just g -> do let u i j = evalSafe (xa, xb, w) (ya, yb, h) g i (h-j)
                     v i j = rgba colorMode (u i j)
                     img = ImageRGBA8 (generateImage v w h)
                 savePngImage "arbplot.png" img
                 case fromDynamicImage img of
                   Just picture -> display (InWindow "arb plot" (w, h) (0, 0))
                                           white picture
                   _ -> putStrLn "could not display picture."
    _ -> putStrLn $ "function '" ++ f ++ "' not available."

rgba colorMode z = PixelRGBA8 r' g' b' alpha where
  (r, g, b) = colorFunction colorMode z
  alpha = if (r, g, b) /= (0.5, 0.5, 0.5) then 255 else 0
  [r', g', b'] = map (min 255 . floor . (*255)) [r, g, b]
  
data Range = Range Double Double Double Double deriving Show
data Size = Size Int Int deriving Show

data Parameters = Parameters {
  xa :: Double,
  xb :: Double,
  ya :: Double,
  yb :: Double,
  with :: Int,
  height :: Int,
  colorMode :: Int,
  fun :: String
  } deriving Show

parameters :: Parser Parameters
parameters = Parameters
  <$> option auto (
      long "xa" <>
      value (-10.0) <>
      showDefault <>
      metavar "XA")
  <*> option auto (
      long "xb" <>
      value 10.0 <>
      showDefault <>
      metavar "XB")
  <*> option auto (
      long "ya" <>
      value (-10.0) <>
      showDefault <>
      metavar "YA") 
  <*> option auto (
      long "yb" <>
      value 10 <>
      showDefault <>
      metavar "YB")
  <*> option auto (
      long "width" <>
      short 'w' <>
      value 512 <>
      showDefault <>
      metavar "WIDTH")
  <*> option auto (
      long "height" <>
      short 'h' <>
      value 512 <>
      showDefault <>
      metavar "HEIGHT")
  <*> option auto (
      long "color-mode" <>
      short 'c' <>
      value 0 <>
      metavar "COLOR-MODE")
  <*> strOption (
      short 'f' <>
      long "function" <>
      help ("possible values: " ++ intercalate ", " (Map.keys functions)) <>
      metavar "FUNCTION")


