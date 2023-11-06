![examples of complex_plot in Flint2-examples](https://hackage.haskell.org/package/Flint2-0.1.0.1/docs/docs/out.png)

# Flint2
**Flint2** provides a thin Haskell wrapper for [Flint](https://flintlib.org) C-library. 

## Installation

- Install the C-library available from [Flint](https://flintlib.org). 
   There are packages available for various operating systems.

- Install the Haskell interface with

```bash
cabal install Flint2 --lib
```

## Quick Start

A simple example for the application of the library is the
factorization of $2^{256}-1$:

```haskell
import Data.Number.Flint

main = print $ factor (2^256 - 1 :: Fmpz)
```

runnnig main prints 

```
[(3,1),(5,1),(17,1),(257,1),(641,1),(65537,1),(274177,1),(6700417,1),(67280421310721,1),(59649589127497217,1),(5704689200685129054721,1)]
```

examples can be found soon @FLINT2-Examples@.
