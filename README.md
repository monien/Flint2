# Flint2
**Flint2** provides a thin Haskell wrapper for [Flint](https://flintlib.org) C-library. 

## Installation

- Install the C-library available from [Flint](https://flintlib.org). 
   There are packages available for various operating systems.

- Install the Haskell interface with

```bash
cabal install Flint2
```

## Quick Start

A simple program using the thin wrapper would be

```haskell
import Data.Number.Flint

main = do 
  x <- newFmpz
  y <- newFmpz
  withFmpz x $ \x -> do
    withFmpz y $ \y -> do
      fmpz_set_ui x 7
      fmpz_set_ui y 6
      fmpz_mul x x y
      fmpz_print x  
```

which will print the numerical value 42.

In the app directory more practical information on how to use the thin wrapper can be found. 
The above example simplifies to 

```haskell
include Fmpz

main = do
  let x = 7 :: Fmpz 
      y = 6 :: Fmpz
  print $ x*y
  print $ factor (42 :: Fmpz)
  
```

which prints 

```
42 
[(2,1),(3,1),(7,1)]
```
