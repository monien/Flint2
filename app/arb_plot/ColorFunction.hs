module ColorFunction where

import Data.List (findIndex)
import Data.Complex

colorFunction mode z
 | not (isInfinite r || isNaN r) = colorFunction' mode z
 | otherwise = (0.5, 0.5, 0.5)
 where r = magnitude z
 
colorFunction' 0 z = toRGB (h, l, s) where
  phi = phase z
  tmp = (phi + pi)/(2*pi) + 1/2
  h = tmp - fromIntegral (floor tmp)
  l | log (magnitude z) >  200 = 1
    | log (magnitude z) < -200 = 0
    | otherwise = 1 - 1 / (1 + (magnitude z) ** 0.2)
  s = 0.8

colorFunction' 1 z = (r, g, b) where
  phi = phase z
  h = max (min (phi/pi) 1) (-1)
  Just j = findIndex ((>h) . head) blueOrangeColors
  [ha, ra, ga, ba] = blueOrangeColors !! (j-1)
  [hb, rb, gb, bb] = blueOrangeColors !! j
  s = (h - ha) / (hb - ha)
  r = ra + (rb - ra) * s
  g = ga + (gb - ga) * s
  b = ba + (bb - ba) * s
  blueOrangeColors = [
   [-1.0,  0.0, 0.0, 0.0],
   [-0.95, 0.1, 0.2, 0.5],
   [-0.5,  0.0, 0.5, 1.0],
   [-0.05, 0.4, 0.8, 0.8],
   [ 0.0,  1.0, 1.0, 1.0],
   [ 0.05, 1.0, 0.9, 0.3],
   [ 0.5,  0.9, 0.5, 0.0],
   [ 0.95, 0.7, 0.1, 0.0],
   [ 1.0,  0.0, 0.0, 0.0],
   [ 2.0,  0.0, 0.0, 0.0]
   ]

colorFunction' mode z
  | mode == 2 = (r, g, b)
  | mode == 3 = mix 0.0 (-0.5) 0.2 0.0 0.0 (-0.1) 0.0 (-1.0) (-0.2)
  | mode == 4 = mix 0.0 (-0.5) 0.2 0.0 0.5 (-0.1) 0.0 (-0.3) (-1.0)
  | mode == 5 = mix 0.0 (-0.5) (-1.0) 0.0 (-0.1) (-0.67) 0.0 (-0.55) (-0.12)
  | mode == 6 = mix 0.86 0.0 0.13 0.57 0.19 (-0.52) 0.31 (-0.30) (-0.94)
  where
    (r1, g1, b1) = colorFunction 0 z
    (r2, g2, b2) = colorFunction 1 z
    f x y = blend x (clamp (dodge x y))
    [r, g, b] = zipWith f [r1, g1, b1] [r2, g2, b2] 
    mix = balance (r, g, b)
    
toRGB (h, l, s)
  | s == 0 = (l, l, l)
  | otherwise = (vv m1 m2 (h+1/3), vv m1 m2 h, vv m1 m2 (h-1/3))
  where
    m2 = if l <= 0.5 then l * (1 + s) else l + s - l*s
    m1 = 2*l - m2  
    vv m1 m2 hue
      | 6*h < 1 = m1 + (m2 - m1)*h*6
      | 2*h < 1 = m2
      | 3*h < 2 = m1 + (m2 - m1)*(2/3 - h)*6
      | otherwise = m1
      where h = hue - fromIntegral (floor hue)

toHLS (r, g, b)
  | hi == lo  = (0,  l, 0)
  | l <= 0.5  = (h', l, d / (hi + lo))
  | otherwise = (h', l, d / (2 - hi - lo))
  where
    hi = max (max r g) b
    lo = min (min r g) b
    l = 0.5 * (lo + hi)
    d = hi -lo
    d' = if d /= 0 then d else 1
    h | r == hi   = (g - b) / d'
      | g == hi   = (b - r) / d' + 2
      | otherwise = (r - g) / d' + 4
    h' = h / 6
    h'' = if h' < 0 then h' + 1 else h'

clamp x = max 0 (min x 1)
blend x y = (x + y)/2
dodge a b = a / ((1 - b) + 1/256)

balanceChannel value x (shadows, midtones, highlights) = value' where
  [a, b, scale] = [1/4, 1/3, 7/10]
  shadows'    = clamp ((x - b) / (-a) + 0.5) * scale * shadows
  midtones'   = clamp ((x - b) /   a  + 0.5) *
                clamp ((x + b - 1.0) / (-a) + 0.5) * scale * midtones
  highlights' = clamp ((x + b - 1.0) /   a  + 0.5) * scale * highlights
  value' = clamp (value + shadows' + midtones' + highlights')

balance (r, g, b) u' u'' u''' v' v'' v''' w' w'' w''' = (r'', g'', b'') where
  [u, v, w] = [(u', u'', u'''), (v', v'', v'''), (w', w'', w''')]
  [r', g', b'] = zipWith (\c x -> balanceChannel c c x) [r, g, b] [u, v, w]
  (h,  l,  s ) = toHLS (r,  g,  b )
  (h', l', s') = toHLS (r', g', b')
  (r'', g'', b'') = toRGB (h', l, s')

hlsFunction 0 z = (h, l, s) where
  x = realPart z
  y = imagPart z
  phi = atan2 y x
  tmp = (phi + pi)/(2*pi) + 1/2
  h = tmp - fromIntegral (floor tmp)
  l | log(magnitude z) >  138 = 1
    | log(magnitude z) < -138 = 0
    | otherwise = 1 - 1 / (1 + (magnitude z) ** 0.2)
  s = 0.8
