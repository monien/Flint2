{-# language
    CApiFFI
  , FlexibleInstances
  , ForeignFunctionInterface
  , MultiParamTypeClasses
  , TupleSections
  , TypeFamilies
  , ScopedTypeVariables
  #-}

module Data.Number.Flint.Groups.Qfb.FFI (
  -- * Binary quadratic forms
    Qfb (..)
  , CQfb (..)
  , newQfb
  , withQfb
  , withNewQfb
  -- * Memory management
  , qfb_init
  , qfb_clear
  , qfb_array_clear
  -- * Hash table
  , qfb_hash_init
  , qfb_hash_clear
  , qfb_hash_insert
  , qfb_hash_find
  -- * Basic manipulation
  , qfb_set
  -- * Comparison
  , qfb_equal
  -- * Input\/output
  , qfb_get_str
  , qfb_fprint
  , qfb_print
  -- * Computing with forms
  , qfb_discriminant
  , qfb_reduce
  , qfb_is_reduced
  , qfb_reduced_forms
  , qfb_reduced_forms_large
  , qfb_nucomp
  , qfb_nudupl
  , qfb_pow_ui
  , qfb_pow
  , qfb_inverse
  , qfb_is_principal_form
  , qfb_principal_form
  , qfb_is_primitive
  , qfb_prime_form
  , qfb_exponent_element
  , qfb_exponent
  , qfb_exponent_grh
) where 

-- Binary quadratic forms ------------------------------------------------------

import Foreign.Ptr
import Foreign.ForeignPtr
import Foreign.Storable
import Foreign.C.Types
import Foreign.C.String
import Foreign.Marshal.Array
import Foreign.Marshal.Alloc

import Data.Number.Flint.Flint
import Data.Number.Flint.Fmpz
import Data.Number.Flint.Fmpz.Mat
import Data.Number.Flint.Fmpz.Poly
import Data.Number.Flint.Fmpz.MPoly

import Data.Number.Flint.Fmpq
import Data.Number.Flint.Fmpq.Poly

import Data.Number.Flint.Arb.Types
import Data.Number.Flint.Acb.Types

#include <flint/qfb.h>

-- qfb_t -----------------------------------------------------------------------

data Qfb = Qfb {-# UNPACK #-} !(ForeignPtr CQfb)
data CQfb = CQfb (Ptr CFmpz) (Ptr CFmpz) (Ptr CFmpz)

instance Storable CQfb where
  {-# INLINE sizeOf #-}
  sizeOf    _ = #{size      qfb_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment qfb_t}
  peek ptr = do
    let q = castPtr ptr :: Ptr CFmpz
    return $ CQfb q (q `advancePtr` 1) (q `advancePtr` 2)
   
  poke = error "CQfb.poke: undefined."

-- | Create a Qfb.
newQfb a b c = do
  p <- mallocForeignPtr
  withForeignPtr p $ \p -> do
    qfb_init p
    CQfb ap bp cp <- peek p
    withFmpz a $ \a -> fmpz_set ap a
    withFmpz b $ \b -> fmpz_set bp b
    withFmpz c $ \c -> fmpz_set cp c
  addForeignPtrFinalizer p_qfb_clear p
  return $ Qfb p

-- | Use Qfb in `f`.
{-# INLINE withQfb #-}
withQfb (Qfb p) f = do
  withForeignPtr p $ \fp -> (Qfb p,) <$> f fp

-- | Apply `f` to new Qfb.
{-# INLINE withNewQfb #-}
withNewQfb a b c f = do
  x <- newQfb a b c
  withQfb x f

-- Memory management -----------------------------------------------------------

-- | /qfb_init/ /q/ 
-- 
-- Initialise a code{qfb_t} \(q\) for use.
foreign import ccall "qbf.h qfb_init"
  qfb_init :: Ptr CQfb -> IO ()

-- | /qfb_clear/ /q/ 
-- 
-- Clear a code{qfb_t} after use. This releases any memory allocated for
-- \(q\) back to flint.
foreign import ccall "qbf.h qfb_clear"
  qfb_clear :: Ptr CQfb -> IO ()

foreign import ccall "qbf.h &qfb_clear"
  p_qfb_clear :: FunPtr (Ptr CQfb -> IO ())

-- | /qfb_array_clear/ /forms/ /num/ 
-- 
-- Clean up an array of code{qfb} structs allocated by a qfb function. The
-- parameter code{num} must be set to the length of the array.
foreign import ccall "qbf.h qfb_array_clear"
  qfb_array_clear :: Ptr (Ptr CQfb) -> CLong -> IO ()

-- Hash table ------------------------------------------------------------------

data QfbHash = QfbHash {-# UNPACK #-} !(ForeignPtr CQfbHash)
type CQfbHash = CFlint QfbHash

-- | /qfb_hash_init/ /depth/ 
-- 
-- Initialises a hash table of size \(2^{depth}\).
foreign import ccall "qbf.h qfb_hash_init"
  qfb_hash_init :: CLong -> IO (Ptr (Ptr CQfbHash))

-- | /qfb_hash_clear/ /qhash/ /depth/ 
-- 
-- Frees all memory used by a hash table of size \(2^{depth}\).
foreign import ccall "qbf.h qfb_hash_clear"
  qfb_hash_clear :: Ptr (Ptr CQfbHash) -> CLong -> IO ()

-- | /qfb_hash_insert/ /qhash/ /q/ /q2/ /iter/ /depth/ 
-- 
-- Insert the binary quadratic form code{q} into the given hash table of
-- size \(2^{depth}\) in the field code{q} of the hash structure. Also
-- store the second binary quadratic form code{q2} (if not code{NULL}) in
-- the similarly named field and code{iter} in the similarly named field of
-- the hash structure.
foreign import ccall "qbf.h qfb_hash_insert"
  qfb_hash_insert :: Ptr (Ptr CQfbHash) -> Ptr CQfb -> Ptr CQfb -> CLong -> CLong -> IO ()

-- | /qfb_hash_find/ /qhash/ /q/ /depth/ 
-- 
-- Search for the given binary quadratic form or its inverse in the given
-- hash table of size \(2^{depth}\). If it is found, return the index in
-- the table (which is an array of code{qfb_hash_t} structs, otherwise
-- return code{-1L}.
foreign import ccall "qbf.h qfb_hash_find"
  qfb_hash_find :: Ptr (Ptr CQfbHash) -> Ptr CQfb -> CLong -> IO CLong

-- Basic manipulation ----------------------------------------------------------

-- | /qfb_set/ /f/ /g/ 
-- 
-- Set the binary quadratic form \(f\) to be equal to \(g\).
foreign import ccall "qbf.h qfb_set"
  qfb_set :: Ptr CQfb -> Ptr CQfb -> IO ()

-- Comparison ------------------------------------------------------------------

-- | /qfb_equal/ /f/ /g/ 
-- 
-- Returns \(1\) if \(f\) and \(g\) are identical binary quadratic forms,
-- otherwise returns \(0\).
foreign import ccall "qbf.h qfb_equal"
  qfb_equal :: Ptr CQfb -> Ptr CQfb -> IO CInt

-- Input\/output ---------------------------------------------------------------

foreign import ccall "qfb.h qfb_get_str"
  qfb_get_str :: Ptr CQfb -> IO CString

foreign import ccall "qfb.h qfb_fprint"
  qfb_fprint :: Ptr CFile -> Ptr CQfb -> IO CString

-- | /qfb_print/ /q/ 
-- 
-- Print a binary quadratic form \(q\) in the format \((a, b, c)\) where
-- \(a\), \(b\), \(c\) are the entries of \(q\).
qfb_print :: Ptr CQfb -> IO ()
qfb_print x = do
  cs <- qfb_get_str x
  s <- peekCString cs
  free cs
  putStr s
  
-- Computing with forms --------------------------------------------------------

-- | /qfb_discriminant/ /D/ /f/ 
-- 
-- Set \(D\) to the discriminant of the binary quadratic form \(f\), i.e.
-- to \(b^2 - 4ac\), where \(f = (a, b, c)\).
foreign import ccall "qbf.h qfb_discriminant"
  qfb_discriminant :: Ptr CFmpz -> Ptr CQfb -> IO ()

-- | /qfb_reduce/ /r/ /f/ /D/ 
-- 
-- Set \(r\) to the reduced form equivalent to the binary quadratic form
-- \(f\) of discriminant \(D\).
foreign import ccall "qbf.h qfb_reduce"
  qfb_reduce :: Ptr CQfb -> Ptr CQfb -> Ptr CFmpz -> IO ()

-- | /qfb_is_reduced/ /r/ 
-- 
-- Returns \(1\) if \(q\) is a reduced binary quadratic form. Otherwise
-- returns \(1\).
foreign import ccall "qbf.h qfb_is_reduced"
  qfb_is_reduced :: Ptr CQfb -> IO CInt

-- | /qfb_reduced_forms/ /forms/ /d/ 
-- 
-- Given a discriminant \(d\) (negative for negative definite forms),
-- compute all the reduced binary quadratic forms of that discriminant. The
-- function allocates space for these and returns it in the variable
-- code{forms} (the user is responsible for cleaning this up by a single
-- call to code{qfb_array_clear} on code{forms}, after use. The function
-- returns the number of forms generated (the form class number). The forms
-- are stored in an array of code{qfb} structs, which contain fields
-- code{a, b, c} corresponding to forms \((a, b, c)\).
foreign import ccall "qbf.h qfb_reduced_forms"
  qfb_reduced_forms :: Ptr (Ptr CQfb) -> CLong -> IO CLong

-- | /qfb_reduced_forms_large/ /forms/ /d/ 
-- 
-- As for @qfb_reduced_forms@. However, for small \(|d|\) it requires fewer
-- primes to be computed at a small cost in speed. It is called
-- automatically by code{qfb_reduced_forms} for large \(|d|\) so that
-- @flint_primes@ is not exhausted.
foreign import ccall "qbf.h qfb_reduced_forms_large"
  qfb_reduced_forms_large :: Ptr (Ptr CQfb) -> CLong -> IO CLong

-- | /qfb_nucomp/ /r/ /f/ /g/ /D/ /L/ 
-- 
-- Shanks\' NUCOMP as described in~citep{JacvdP}
-- 
-- % Computational aspects of NUCOMP\", Michael J. Jacobson Jr., % Alfred
-- J. van der Poorten, ANTS 2002, LNCS 2369, pp. 120--133.
-- 
-- Computes the near reduced composition of forms \(f\) and \(g\) given
-- \(L = \lfloor |D|^{1/4} \rfloor\) where \(D\) is the common discriminant
-- of \(f\) and \(g\). The result is returned in \(r\).
-- 
-- We require that that \(f\) is a primitive form.
foreign import ccall "qbf.h qfb_nucomp"
  qfb_nucomp :: Ptr CQfb -> Ptr CQfb -> Ptr CQfb -> Ptr CFmpz -> Ptr CFmpz -> IO ()

-- | /qfb_nudupl/ /r/ /f/ /D/ /L/ 
-- 
-- As for code{nucomp} except that the form \(f\) is composed with itself.
-- We require that that \(f\) is a primitive form.
foreign import ccall "qbf.h qfb_nudupl"
  qfb_nudupl :: Ptr CQfb -> Ptr CQfb -> Ptr CFmpz -> Ptr CFmpz -> IO ()

-- | /qfb_pow_ui/ /r/ /f/ /D/ /exp/ 
-- 
-- Compute the near reduced form \(r\) which is the result of composing the
-- principal form (identity) with \(f\) code{exp} times.
-- 
-- We require \(D\) to be set to the discriminant of \(f\) and that \(f\)
-- is a primitive form.
foreign import ccall "qbf.h qfb_pow_ui"
  qfb_pow_ui :: Ptr CQfb -> Ptr CQfb -> Ptr CFmpz -> CULong -> IO ()

-- | /qfb_pow/ /r/ /f/ /D/ /exp/ 
-- 
-- As per code{qfb_pow_ui}.
foreign import ccall "qbf.h qfb_pow"
  qfb_pow :: Ptr CQfb -> Ptr CQfb -> Ptr CFmpz -> Ptr CFmpz -> IO ()

-- | /qfb_inverse/ /r/ /f/ 
-- 
-- Set \(r\) to the inverse of the binary quadratic form \(f\).
foreign import ccall "qbf.h qfb_inverse"
  qfb_inverse :: Ptr CQfb -> Ptr CQfb -> IO ()

-- | /qfb_is_principal_form/ /f/ /D/ 
-- 
-- Return \(1\) if \(f\) is the reduced principal form of discriminant
-- \(D\), i.e. the identity in the form class group.
foreign import ccall "qbf.h qfb_is_principal_form"
  qfb_is_principal_form :: Ptr CQfb -> Ptr CFmpz -> IO CInt

-- | /qfb_principal_form/ /f/ /D/ 
-- 
-- Set \(f\) to the principal form of discriminant \(D\), i.e. the identity
-- in the form class group.
foreign import ccall "qbf.h qfb_principal_form"
  qfb_principal_form :: Ptr CQfb -> Ptr CFmpz -> IO ()

-- | /qfb_is_primitive/ /f/ 
-- 
-- Return \(1\) if \(f\) is primitive, i.e. the greatest common divisor of
-- its three coefficients is \(1\). Otherwise the function returns \(0\).
foreign import ccall "qbf.h qfb_is_primitive"
  qfb_is_primitive :: Ptr CQfb -> IO CInt

-- | /qfb_prime_form/ /r/ /D/ /p/ 
-- 
-- Sets \(r\) to the unique prime \((p, b, c)\) of discriminant \(D\), i.e.
-- with \(0 < b \leq p\). We require that \(p\) is a prime.
foreign import ccall "qbf.h qfb_prime_form"
  qfb_prime_form :: Ptr CQfb -> Ptr CFmpz -> Ptr CFmpz -> IO ()

-- | /qfb_exponent_element/ /exponent/ /f/ /n/ /B1/ /B2_sqrt/ 
-- 
-- Find the exponent of the element \(f\) in the form class group of forms
-- of discriminant \(n\), doing a stage \(1\) with primes up to at least
-- code{B1} and a stage \(2\) for a single large prime up to at least the
-- square of code{B2}. If the function fails to find the exponent it
-- returns \(0\), otherwise the function returns \(1\) and code{exponent}
-- is set to the exponent of \(f\), i.e. the minimum power of \(f\) which
-- gives the identity.
-- 
-- It is assumed that the form \(f\) is reduced. We require that
-- code{iters} is a power of \(2\) and that code{iters} >= 1024.
-- 
-- The function performs a stage \(2\) which stores up to \(4\times\)
-- code{iters} binary quadratic forms, and \(12\times\) code{iters}
-- additional limbs of data in a hash table, where code{iters} is the
-- square root of code{B2}.
foreign import ccall "qbf.h qfb_exponent_element"
  qfb_exponent_element :: Ptr CFmpz -> Ptr CQfb -> Ptr CFmpz -> CULong -> CULong -> IO CInt

-- | /qfb_exponent/ /exponent/ /n/ /B1/ /B2_sqrt/ /c/ 
-- 
-- Compute the exponent of the class group of discriminant \(n\), doing a
-- stage \(1\) with primes up to at least code{B1} and a stage \(2\) for a
-- single large prime up to at least the square of code{B2_sqrt}, and with
-- probability at least \(1 - 2^{-c}\). If the prime limits are exhausted
-- without finding the exponent, the function returns \(0\), otherwise it
-- returns \(1\) and code{exponent} is set to the computed exponent, i.e.
-- the minimum power which every element of the class group has to be
-- raised to give the identity.
-- 
-- The function performs a stage \(2\) which stores up to \(4\times\)
-- code{iters} binary quadratic forms, and \(12\times\) code{iters}
-- additional limbs of data in a hash table, where code{iters} is the
-- square root of code{B2}.
-- 
-- We use algorithm 8.1 of~citep{SuthThesis}
-- 
-- % \"Order Computations in Generic Groups\", Andrew Sutherland, % MIT
-- Thesis 2007. %
-- <http://groups.csail.mit.edu/cis/theses/sutherland-phd.pdf>
foreign import ccall "qbf.h qfb_exponent"
  qfb_exponent :: Ptr CFmpz -> Ptr CFmpz -> CULong -> CULong -> CLong -> IO CInt

-- | /qfb_exponent_grh/ /exponent/ /n/ /iters/ /B1/ /B2_sqrt/ 
-- 
-- As per code{qfb_exponent} except that the bound code{c} is automatically
-- generated such that the exponent it guaranteed to be correct, if found,
-- assuming the GRH, namely that the class group is generated by primes
-- less than \(6\log^2(|n|)\) as per~citep{BuchDull1992}
-- 
-- % \"Distributed Class Group Computation\", Johannes Buchmann, Stephan %
-- D\"{u}llman, Informatik 1 (1992), pp. 69--79.
foreign import ccall "qbf.h qfb_exponent_grh"
  qfb_exponent_grh :: Ptr CFmpz -> Ptr CFmpz -> CULong -> CULong -> CULong -> IO CInt

