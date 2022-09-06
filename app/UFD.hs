module UFD where

class (Num a) => UFD a where
  factor :: a -> [(a, Int)]
  unfactor :: [(a, Int)] -> a
  unfactor x = product $ map (uncurry (^)) x
