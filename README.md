# Flint2
Flint2 provide a thin Haskell wrapper for [Flint](https://flintlib.org) C library. 

## Installation

```bash
stack install
stack haddock
```

## Quick Start

```haskell
import Data.Number.Flint

main = do 
  x <- newFmpz
  withFmpz x $ \x -> do
    fmpz_set_ui x 7
    fmpz_mul x x x
    fmpz_print x  
```

will print the numerical value of 4.

In the app directory more practical information on how to use the thin wrapper can be found. 
The above example simplifies to 

include Fmpz

main = do
  let x = 7 :: Fmpz 
  print $ x*x
