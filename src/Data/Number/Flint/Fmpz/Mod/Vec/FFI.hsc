module Data.Number.Flint.Fmpz.Mod.Vec.FFI (
  -- * Vectors over integers mod n
  -- * Conversions
    _fmpz_mod_vec_set_fmpz_vec
  -- * Arithmetic
  , _fmpz_mod_vec_neg
  , _fmpz_mod_vec_add
  , _fmpz_mod_vec_sub
  -- * Scalar Multiplication
  , _fmpz_mod_vec_scalar_mul_fmpz_mod
  , _fmpz_mod_vec_scalar_addmul_fmpz_mod
  , _fmpz_mod_vec_scalar_div_fmpz_mod
  -- * Dot Product
  , _fmpz_mod_vec_dot
  , _fmpz_mod_vec_dot_rev
  -- * Multiplication
  , _fmpz_mod_vec_mul
) where

-- Vectors over integers mod n -------------------------------------------------

import Foreign.Ptr
import Foreign.C.Types

import Data.Number.Flint.Fmpz
import Data.Number.Flint.Fmpz.Mod

-- Conversions -----------------------------------------------------------------

-- | /_fmpz_mod_vec_set_fmpz_vec/ /A/ /B/ /len/ /ctx/ 
--
-- Set the \(fmpz_mod_vec\) \((A, len)\) to the \(fmpz_vec\) \((B, len)\)
-- after reduction of each entry modulo the modulus..
foreign import ccall "fmpz_mod_vec.h _fmpz_mod_vec_set_fmpz_vec"
  _fmpz_mod_vec_set_fmpz_vec :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpzModCtx -> IO ()

-- Arithmetic ------------------------------------------------------------------

-- | /_fmpz_mod_vec_neg/ /A/ /B/ /len/ /ctx/ 
--
-- Set \((A, len)\) to \(-(B, len)\).
foreign import ccall "fmpz_mod_vec.h _fmpz_mod_vec_neg"
  _fmpz_mod_vec_neg :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpzModCtx -> IO ()

-- | /_fmpz_mod_vec_add/ /a/ /b/ /c/ /n/ /ctx/ 
--
-- Set (A, len) to :math:(B, len) + (C, len)\`.
foreign import ccall "fmpz_mod_vec.h _fmpz_mod_vec_add"
  _fmpz_mod_vec_add :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpzModCtx -> IO ()

-- | /_fmpz_mod_vec_sub/ /a/ /b/ /c/ /n/ /ctx/ 
--
-- Set (A, len) to :math:(B, len) - (C, len)\`.
foreign import ccall "fmpz_mod_vec.h _fmpz_mod_vec_sub"
  _fmpz_mod_vec_sub :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpzModCtx -> IO ()

-- Scalar Multiplication -------------------------------------------------------

-- | /_fmpz_mod_vec_scalar_mul_fmpz_mod/ /A/ /B/ /len/ /c/ /ctx/ 
--
-- Set \((A, len)\) to \((B, len)*c\).
foreign import ccall "fmpz_mod_vec.h _fmpz_mod_vec_scalar_mul_fmpz_mod"
  _fmpz_mod_vec_scalar_mul_fmpz_mod :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> Ptr CFmpzModCtx -> IO ()

-- | /_fmpz_mod_vec_scalar_addmul_fmpz_mod/ /A/ /B/ /len/ /c/ /ctx/ 
--
-- Set \((A, len)\) to \((A, len) + (B, len)*c\).
foreign import ccall "fmpz_mod_vec.h _fmpz_mod_vec_scalar_addmul_fmpz_mod"
  _fmpz_mod_vec_scalar_addmul_fmpz_mod :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> Ptr CFmpzModCtx -> IO ()

-- | /_fmpz_mod_vec_scalar_div_fmpz_mod/ /A/ /B/ /len/ /c/ /ctx/ 
--
-- Set \((A, len)\) to \((B, len)/c\) assuming \(c\) is nonzero.
foreign import ccall "fmpz_mod_vec.h _fmpz_mod_vec_scalar_div_fmpz_mod"
  _fmpz_mod_vec_scalar_div_fmpz_mod :: Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpz -> Ptr CFmpzModCtx -> IO ()

-- Dot Product -----------------------------------------------------------------

-- | /_fmpz_mod_vec_dot/ /d/ /A/ /B/ /len/ /ctx/ 
--
-- Set \(d\) to the dot product of \((A, len)\) with \((B, len)\).
foreign import ccall "fmpz_mod_vec.h _fmpz_mod_vec_dot"
  _fmpz_mod_vec_dot :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpzModCtx -> IO ()

-- | /_fmpz_mod_vec_dot_rev/ /d/ /A/ /B/ /len/ /ctx/ 
--
-- Set \(d\) to the dot product of \((A, len)\) with the reverse of the
-- vector \((B, len)\).
foreign import ccall "fmpz_mod_vec.h _fmpz_mod_vec_dot_rev"
  _fmpz_mod_vec_dot_rev :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpzModCtx -> IO ()

-- Multiplication --------------------------------------------------------------

-- | /_fmpz_mod_vec_mul/ /A/ /B/ /C/ /len/ /ctx/ 
--
-- Set \((A, len)\) the pointwise multiplication of \((B, len)\) and
-- \((C, len)\).
foreign import ccall "fmpz_mod_vec.h _fmpz_mod_vec_mul"
  _fmpz_mod_vec_mul :: Ptr CFmpz -> Ptr CFmpz -> Ptr CFmpz -> CLong -> Ptr CFmpzModCtx -> IO ()

