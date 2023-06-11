{-# language
    CApiFFI
  , FlexibleInstances
  , ForeignFunctionInterface
  , MultiParamTypeClasses
  , TupleSections
  , TypeFamilies
  , ScopedTypeVariables
  #-}
  
module Data.Number.Flint.NF.Elem.FFI (
  -- * __nf_elem.h__ -- number field elements
    NFElem (..)
  , CNFElem (..)
  , newNFElem
  , withNFElem
  -- * Initialisation
  , nf_elem_init
  , nf_elem_clear
  , nf_elem_randtest
  , nf_elem_canonicalise
  , _nf_elem_reduce
  , nf_elem_reduce
  , _nf_elem_invertible_check
  -- * Conversion
  , nf_elem_set_fmpz_mat_row
  , nf_elem_get_fmpz_mat_row
  , nf_elem_set_fmpq_poly
  , nf_elem_get_fmpq_poly
  , nf_elem_get_nmod_poly_den
  , nf_elem_get_nmod_poly
  , nf_elem_get_fmpz_mod_poly_den
  , nf_elem_get_fmpz_mod_poly
  -- * Basic manipulation
  , nf_elem_set_den
  , nf_elem_get_den
  , _nf_elem_set_coeff_num_fmpz
  -- * Comparison
  , _nf_elem_equal
  , nf_elem_equal
  , nf_elem_is_zero
  , nf_elem_is_one
  -- * I\/O
  , nf_elem_get_str_pretty
  , nf_elem_print_pretty
  -- * Arithmetic
  , nf_elem_zero
  , nf_elem_one
  , nf_elem_set
  , nf_elem_neg
  , nf_elem_swap
  , nf_elem_mul_gen
  , _nf_elem_add
  , nf_elem_add
  , _nf_elem_sub
  , nf_elem_sub
  , _nf_elem_mul
  , _nf_elem_mul_red
  , nf_elem_mul
  , nf_elem_mul_red
  , _nf_elem_inv
  , nf_elem_inv
  , _nf_elem_div
  , nf_elem_div
  , _nf_elem_pow
  , nf_elem_pow
  , _nf_elem_norm
  , nf_elem_norm
  , nf_elem_norm_div
  , _nf_elem_norm_div
  , _nf_elem_trace
  , nf_elem_trace
  -- * Representation matrix
  , nf_elem_rep_mat
  , nf_elem_rep_mat_fmpz_mat_den
  -- * Modular reduction
  , nf_elem_mod_fmpz_den
  , nf_elem_smod_fmpz_den
  , nf_elem_mod_fmpz
  , nf_elem_smod_fmpz
  , nf_elem_coprime_den
  , nf_elem_coprime_den_signed
) where 

-- Number field elements -------------------------------------------------------

import Foreign.C.Types
import Foreign.C.String
import Foreign.ForeignPtr
import Foreign.Ptr
import Foreign.Storable
import Foreign.Marshal.Alloc (free)

import Data.Number.Flint.Flint
import Data.Number.Flint.Fmpz
import Data.Number.Flint.Fmpz.Mod.Poly
import Data.Number.Flint.Fmpq
import Data.Number.Flint.Fmpq.Poly
import Data.Number.Flint.Fmpz.Mat
import Data.Number.Flint.Fmpq.Mat
import Data.Number.Flint.NMod.Types
import Data.Number.Flint.NF

#include <flint/nf_elem.h>

-- nf_elem_t -------------------------------------------------------------------

data NFElem = NFElem !(ForeignPtr CNFElem)
data CNFElem = CNFElem

instance Storable CNFElem where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size nf_elem_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment nf_elem_t}
  peek = error "CNFElem.peek is not defined."
  poke = error "CNFElem.poke is not defined."

--------------------------------------------------------------------------------

newNFElem nf@(NF pnf) = do
  x <- mallocForeignPtr
  withForeignPtr x $ \x -> do
    withNF nf $ \nf -> do
      nf_elem_init x nf
      addForeignPtrFinalizerEnv p_nf_elem_clear x pnf
  return $ NFElem x

-- | Use number-field element.
{-# INLINE withNFElem #-}
withNFElem (NFElem p) f = do
  withForeignPtr p $ \fp -> (NFElem p,) <$> f fp
  
--------------------------------------------------------------------------------

-- | /nf_elem_init/ /a/ /nf/ 
-- 
-- Initialise a number field element to belong to the given number field
-- code{nf}. The element is set to zero.
foreign import ccall "nf_elem.h nf_elem_init"
  nf_elem_init :: Ptr CNFElem -> Ptr CNF -> IO ()

-- | /nf_elem_clear/ /a/ /nf/ 
-- 
-- Clear resources allocated by the given number field element in the given
-- number field.
foreign import ccall "nf_elem.h nf_elem_clear"
  nf_elem_clear :: Ptr CNFElem -> Ptr CNF -> IO ()

foreign import ccall "nf_elem.h &nf_elem_clear"
  p_nf_elem_clear :: FunPtr (Ptr CNFElem -> Ptr CNF -> IO ())

-- | /nf_elem_randtest/ /a/ /state/ /bits/ /nf/ 
-- 
-- Generate a random number field element \(a\) in the number field
-- code{nf} whose coefficients have up to the given number of bits.
foreign import ccall "nf_elem.h nf_elem_randtest"
  nf_elem_randtest :: Ptr CNFElem -> Ptr CFRandState -> CMpBitCnt -> Ptr CNF -> IO ()

-- | /nf_elem_canonicalise/ /a/ /nf/ 
-- 
-- Canonicalise a number field element, i.e. reduce numerator and
-- denominator to lowest terms. If the numerator is \(0\), set the
-- denominator to \(1\).
foreign import ccall "nf_elem.h nf_elem_canonicalise"
  nf_elem_canonicalise :: Ptr CNFElem -> Ptr CNF -> IO ()

-- | /_nf_elem_reduce/ /a/ /nf/ 
-- 
-- Reduce a number field element modulo the defining polynomial. This is
-- used with functions such as code{nf_elem_mul_red} which allow reduction
-- to be delayed. Does not canonicalise.
foreign import ccall "nf_elem.h _nf_elem_reduce"
  _nf_elem_reduce :: Ptr CNFElem -> Ptr CNF -> IO ()

-- | /nf_elem_reduce/ /a/ /nf/ 
-- 
-- Reduce a number field element modulo the defining polynomial. This is
-- used with functions such as code{nf_elem_mul_red} which allow reduction
-- to be delayed.
foreign import ccall "nf_elem.h nf_elem_reduce"
  nf_elem_reduce :: Ptr CNFElem -> Ptr CNF -> IO ()

-- | /_nf_elem_invertible_check/ /a/ /nf/ 
-- 
-- Whilst the defining polynomial for a number field should by definition
-- be irreducible, it is not enforced. Thus in test code, it is convenient
-- to be able to check that a given number field element is invertible
-- modulo the defining polynomial of the number field. This function does
-- precisely this.
-- 
-- If \(a\) is invertible modulo the defining polynomial of code{nf} the
-- value \(1\) is returned, otherwise \(0\) is returned.
-- 
-- The function is only intended to be used in test code.
foreign import ccall "nf_elem.h _nf_elem_invertible_check"
  _nf_elem_invertible_check :: Ptr CNFElem -> Ptr CNF -> IO CInt

-- Conversion ------------------------------------------------------------------

-- | /nf_elem_set_fmpz_mat_row/ /b/ /M/ /i/ /den/ /nf/ 
-- 
-- Set \(b\) to the element specified by row \(i\) of the matrix \(M\) and
-- with the given denominator \(d\). Column \(0\) of the matrix corresponds
-- to the constant coefficient of the number field element.
foreign import ccall "nf_elem.h nf_elem_set_fmpz_mat_row"
  nf_elem_set_fmpz_mat_row :: Ptr CNFElem -> Ptr CFmpzMat -> CInt -> Ptr CFmpz -> Ptr CNF -> IO ()

-- | /nf_elem_get_fmpz_mat_row/ /M/ /i/ /den/ /b/ /nf/ 
-- 
-- Set the row \(i\) of the matrix \(M\) to the coefficients of the
-- numerator of the element \(b\) and \(d\) to the denominator of \(b\).
-- Column \(0\) of the matrix corresponds to the constant coefficient of
-- the number field element.
foreign import ccall "nf_elem.h nf_elem_get_fmpz_mat_row"
  nf_elem_get_fmpz_mat_row :: Ptr CFmpzMat -> CInt -> Ptr CFmpz -> Ptr CNFElem -> Ptr CNF -> IO ()

-- | /nf_elem_set_fmpq_poly/ /a/ /pol/ /nf/ 
-- 
-- Set \(a\) to the element corresponding to the polynomial code{pol}.
foreign import ccall "nf_elem.h nf_elem_set_fmpq_poly"
  nf_elem_set_fmpq_poly :: Ptr CNFElem -> Ptr CFmpqPoly -> Ptr CNF -> IO ()

-- | /nf_elem_get_fmpq_poly/ /pol/ /a/ /nf/ 
-- 
-- Set code{pol} to a polynomial corresponding to \(a\), reduced modulo the
-- defining polynomial of code{nf}.
foreign import ccall "nf_elem.h nf_elem_get_fmpq_poly"
  nf_elem_get_fmpq_poly :: Ptr CFmpqPoly -> Ptr CNFElem -> Ptr CNF -> IO ()

-- | /nf_elem_get_nmod_poly_den/ /pol/ /a/ /nf/ /den/ 
-- 
-- Set code{pol} to the reduction of the polynomial corresponding to the
-- numerator of \(a\). If code{den == 1}, the result is multiplied by the
-- inverse of the denominator of \(a\). In this case it is assumed that the
-- reduction of the denominator of \(a\) is invertible.
foreign import ccall "nf_elem.h nf_elem_get_nmod_poly_den"
  nf_elem_get_nmod_poly_den :: Ptr CNModPoly -> Ptr CNFElem -> Ptr CNF -> CInt -> IO ()

-- | /nf_elem_get_nmod_poly/ /pol/ /a/ /nf/ 
-- 
-- Set code{pol} to the reduction of the polynomial corresponding to the
-- numerator of \(a\). The result is multiplied by the inverse of the
-- denominator of \(a\). It is assumed that the reduction of the
-- denominator of \(a\) is invertible.
foreign import ccall "nf_elem.h nf_elem_get_nmod_poly"
  nf_elem_get_nmod_poly :: Ptr CNModPoly -> Ptr CNFElem -> Ptr CNF -> IO ()

-- | /nf_elem_get_fmpz_mod_poly_den/ /pol/ /a/ /nf/ /den/ 
-- 
-- Set code{pol} to the reduction of the polynomial corresponding to the
-- numerator of \(a\). If code{den == 1}, the result is multiplied by the
-- inverse of the denominator of \(a\). In this case it is assumed that the
-- reduction of the denominator of \(a\) is invertible.
foreign import ccall "nf_elem.h nf_elem_get_fmpz_mod_poly_den"
  nf_elem_get_fmpz_mod_poly_den :: Ptr CFmpzModPoly -> Ptr CNFElem -> Ptr CNF -> CInt -> IO ()

-- | /nf_elem_get_fmpz_mod_poly/ /pol/ /a/ /nf/ 
-- 
-- Set code{pol} to the reduction of the polynomial corresponding to the
-- numerator of \(a\). The result is multiplied by the inverse of the
-- denominator of \(a\). It is assumed that the reduction of the
-- denominator of \(a\) is invertible.
foreign import ccall "nf_elem.h nf_elem_get_fmpz_mod_poly"
  nf_elem_get_fmpz_mod_poly :: Ptr CFmpzModPoly -> Ptr CNFElem -> Ptr CNF -> IO ()

-- Basic manipulation ----------------------------------------------------------

-- | /nf_elem_set_den/ /b/ /d/ /nf/ 
-- 
-- Set the denominator of the code{nf_elem_t b} to the given integer \(d\).
-- Assumes \(d > 0\).
foreign import ccall "nf_elem.h nf_elem_set_den"
  nf_elem_set_den :: Ptr CNFElem -> Ptr CFmpz -> Ptr CNF -> IO ()

-- | /nf_elem_get_den/ /d/ /b/ /nf/ 
-- 
-- Set \(d\) to the denominator of the code{nf_elem_t b}.
foreign import ccall "nf_elem.h nf_elem_get_den"
  nf_elem_get_den :: Ptr CFmpz -> Ptr CNFElem -> Ptr CNF -> IO ()

-- | /_nf_elem_set_coeff_num_fmpz/ /a/ /i/ /d/ /nf/ 
-- 
-- Set the \(i`th coefficient of the denominator of :math:`a\) to the given
-- integer \(d\).
foreign import ccall "nf_elem.h _nf_elem_set_coeff_num_fmpz"
  _nf_elem_set_coeff_num_fmpz :: Ptr CNFElem -> CLong -> Ptr CFmpz -> Ptr CNF -> IO ()

-- Comparison ------------------------------------------------------------------

-- | /_nf_elem_equal/ /a/ /b/ /nf/ 
-- 
-- Return \(1\) if the given number field elements are equal in the given
-- number field code{nf}. This function does emph{not} assume \(a\) and
-- \(b\) are canonicalised.
foreign import ccall "nf_elem.h _nf_elem_equal"
  _nf_elem_equal :: Ptr CNFElem -> Ptr CNFElem -> Ptr CNF -> IO CInt

-- | /nf_elem_equal/ /a/ /b/ /nf/ 
-- 
-- Return \(1\) if the given number field elements are equal in the given
-- number field code{nf}. This function assumes \(a\) and \(b\) emph{are}
-- canonicalised.
foreign import ccall "nf_elem.h nf_elem_equal"
  nf_elem_equal :: Ptr CNFElem -> Ptr CNFElem -> Ptr CNF -> IO CInt

-- | /nf_elem_is_zero/ /a/ /nf/ 
-- 
-- Return \(1\) if the given number field element is equal to zero,
-- otherwise return \(0\).
foreign import ccall "nf_elem.h nf_elem_is_zero"
  nf_elem_is_zero :: Ptr CNFElem -> Ptr CNF -> IO CInt

-- | /nf_elem_is_one/ /a/ /nf/ 
-- 
-- Return \(1\) if the given number field element is equal to one,
-- otherwise return \(0\).
foreign import ccall "nf_elem.h nf_elem_is_one"
  nf_elem_is_one :: Ptr CNFElem -> Ptr CNF -> IO CInt

-- I\/O ------------------------------------------------------------------------

foreign import ccall "nf_elem.h nf_elem_get_str_pretty"
  nf_elem_get_str_pretty :: Ptr CNFElem -> CString -> Ptr CNF -> IO CString

-- | /nf_elem_print_pretty/ /a/ /nf/ /var/ 
-- 
-- Print the given number field element to code{stdout} using the
-- null-terminated string code{var} not equal to code{\"0\"} as the name of
-- the primitive element.
-- foreign import ccall "nf_elem.h nf_elem_print_pretty"
nf_elem_print_pretty :: Ptr CNFElem -> Ptr CNF -> CString -> IO ()
nf_elem_print_pretty x nf var = do
  cs <- nf_elem_get_str_pretty x var nf
  s <- peekCString cs
  free cs
  putStr s
  
-- Arithmetic ------------------------------------------------------------------

-- | /nf_elem_zero/ /a/ /nf/ 
-- 
-- Set the given number field element to zero.
foreign import ccall "nf_elem.h nf_elem_zero"
  nf_elem_zero :: Ptr CNFElem -> Ptr CNF -> IO ()

-- | /nf_elem_one/ /a/ /nf/ 
-- 
-- Set the given number field element to one.
foreign import ccall "nf_elem.h nf_elem_one"
  nf_elem_one :: Ptr CNFElem -> Ptr CNF -> IO ()

-- | /nf_elem_set/ /a/ /b/ /nf/ 
-- 
-- Set the number field element \(a\) to equal the number field element
-- \(b\), i.e. set \(a = b\).
foreign import ccall "nf_elem.h nf_elem_set"
  nf_elem_set :: Ptr CNFElem -> Ptr CNFElem -> Ptr CNF -> IO ()

-- | /nf_elem_neg/ /a/ /b/ /nf/ 
-- 
-- Set the number field element \(a\) to minus the number field element
-- \(b\), i.e. set \(a = -b\).
foreign import ccall "nf_elem.h nf_elem_neg"
  nf_elem_neg :: Ptr CNFElem -> Ptr CNFElem -> Ptr CNF -> IO ()

-- | /nf_elem_swap/ /a/ /b/ /nf/ 
-- 
-- Efficiently swap the two number field elements \(a\) and \(b\).
foreign import ccall "nf_elem.h nf_elem_swap"
  nf_elem_swap :: Ptr CNFElem -> Ptr CNFElem -> Ptr CNF -> IO ()

-- | /nf_elem_mul_gen/ /a/ /b/ /nf/ 
-- 
-- Multiply the element \(b\) with the generator of the number field.
foreign import ccall "nf_elem.h nf_elem_mul_gen"
  nf_elem_mul_gen :: Ptr CNFElem -> Ptr CNFElem -> Ptr CNF -> IO ()

-- | /_nf_elem_add/ /r/ /a/ /b/ /nf/ 
-- 
-- Add two elements of a number field code{nf}, i.e. set \(r = a + b\).
-- Canonicalisation is not performed.
foreign import ccall "nf_elem.h _nf_elem_add"
  _nf_elem_add :: Ptr CNFElem -> Ptr CNFElem -> Ptr CNFElem -> Ptr CNF -> IO ()

-- | /nf_elem_add/ /r/ /a/ /b/ /nf/ 
-- 
-- Add two elements of a number field code{nf}, i.e. set \(r = a + b\).
foreign import ccall "nf_elem.h nf_elem_add"
  nf_elem_add :: Ptr CNFElem -> Ptr CNFElem -> Ptr CNFElem -> Ptr CNF -> IO ()

-- | /_nf_elem_sub/ /r/ /a/ /b/ /nf/ 
-- 
-- Subtract two elements of a number field code{nf}, i.e. set
-- \(r = a - b\). Canonicalisation is not performed.
foreign import ccall "nf_elem.h _nf_elem_sub"
  _nf_elem_sub :: Ptr CNFElem -> Ptr CNFElem -> Ptr CNFElem -> Ptr CNF -> IO ()

-- | /nf_elem_sub/ /r/ /a/ /b/ /nf/ 
-- 
-- Subtract two elements of a number field code{nf}, i.e. set
-- \(r = a - b\).
foreign import ccall "nf_elem.h nf_elem_sub"
  nf_elem_sub :: Ptr CNFElem -> Ptr CNFElem -> Ptr CNFElem -> Ptr CNF -> IO ()

-- | /_nf_elem_mul/ /a/ /b/ /c/ /nf/ 
-- 
-- Multiply two elements of a number field code{nf}, i.e. set
-- \(r = a * b\). Does not canonicalise. Aliasing of inputs with output is
-- not supported.
foreign import ccall "nf_elem.h _nf_elem_mul"
  _nf_elem_mul :: Ptr CNFElem -> Ptr CNFElem -> Ptr CNFElem -> Ptr CNF -> IO ()

-- | /_nf_elem_mul_red/ /a/ /b/ /c/ /nf/ /red/ 
-- 
-- As per code{_nf_elem_mul}, but reduction modulo the defining polynomial
-- of the number field is only carried out if code{red == 1}. Assumes both
-- inputs are reduced.
foreign import ccall "nf_elem.h _nf_elem_mul_red"
  _nf_elem_mul_red :: Ptr CNFElem -> Ptr CNFElem -> Ptr CNFElem -> Ptr CNF -> CInt -> IO ()

-- | /nf_elem_mul/ /a/ /b/ /c/ /nf/ 
-- 
-- Multiply two elements of a number field code{nf}, i.e. set
-- \(r = a * b\).
foreign import ccall "nf_elem.h nf_elem_mul"
  nf_elem_mul :: Ptr CNFElem -> Ptr CNFElem -> Ptr CNFElem -> Ptr CNF -> IO ()

-- | /nf_elem_mul_red/ /a/ /b/ /c/ /nf/ /red/ 
-- 
-- As per code{nf_elem_mul}, but reduction modulo the defining polynomial
-- of the number field is only carried out if code{red == 1}. Assumes both
-- inputs are reduced.
foreign import ccall "nf_elem.h nf_elem_mul_red"
  nf_elem_mul_red :: Ptr CNFElem -> Ptr CNFElem -> Ptr CNFElem -> Ptr CNF -> CInt -> IO ()

-- | /_nf_elem_inv/ /r/ /a/ /nf/ 
-- 
-- Invert an element of a number field code{nf}, i.e. set \(r = a^{-1}\).
-- Aliasing of the input with the output is not supported.
foreign import ccall "nf_elem.h _nf_elem_inv"
  _nf_elem_inv :: Ptr CNFElem -> Ptr CNFElem -> Ptr CNF -> IO ()

-- | /nf_elem_inv/ /r/ /a/ /nf/ 
-- 
-- Invert an element of a number field code{nf}, i.e. set \(r = a^{-1}\).
foreign import ccall "nf_elem.h nf_elem_inv"
  nf_elem_inv :: Ptr CNFElem -> Ptr CNFElem -> Ptr CNF -> IO ()

-- | /_nf_elem_div/ /a/ /b/ /c/ /nf/ 
-- 
-- Set \(a\) to \(b/c\) in the given number field. Aliasing of \(a\) and
-- \(b\) is not permitted.
foreign import ccall "nf_elem.h _nf_elem_div"
  _nf_elem_div :: Ptr CNFElem -> Ptr CNFElem -> Ptr CNFElem -> Ptr CNF -> IO ()

-- | /nf_elem_div/ /a/ /b/ /c/ /nf/ 
-- 
-- Set \(a\) to \(b/c\) in the given number field.
foreign import ccall "nf_elem.h nf_elem_div"
  nf_elem_div :: Ptr CNFElem -> Ptr CNFElem -> Ptr CNFElem -> Ptr CNF -> IO ()

-- | /_nf_elem_pow/ /res/ /a/ /e/ /nf/ 
-- 
-- Set code{res} to \(a^e\) using left-to-right binary exponentiation as
-- described in~citep[p.~461]{Knu1997}.
-- 
-- Assumes that \(a \neq 0\) and \(e > 1\). Does not support aliasing.
foreign import ccall "nf_elem.h _nf_elem_pow"
  _nf_elem_pow :: Ptr CNFElem -> Ptr CNFElem -> CULong -> Ptr CNF -> IO ()

-- | /nf_elem_pow/ /res/ /a/ /e/ /nf/ 
-- 
-- Set code{res} = code{a^e} using the binary exponentiation algorithm. If
-- \(e\) is zero, returns one, so that in particular code{0^0 = 1}.
foreign import ccall "nf_elem.h nf_elem_pow"
  nf_elem_pow :: Ptr CNFElem -> Ptr CNFElem -> CULong -> Ptr CNF -> IO ()

-- | /_nf_elem_norm/ /rnum/ /rden/ /a/ /nf/ 
-- 
-- Set code{{rnum, rden}} to the absolute norm of the given number field
-- element \(a\).
foreign import ccall "nf_elem.h _nf_elem_norm"
  _nf_elem_norm :: Ptr CFmpz -> Ptr CFmpz -> Ptr CNFElem -> Ptr CNF -> IO ()

-- | /nf_elem_norm/ /res/ /a/ /nf/ 
-- 
-- Set code{res} to the absolute norm of the given number field element
-- \(a\).
foreign import ccall "nf_elem.h nf_elem_norm"
  nf_elem_norm :: Ptr CFmpq -> Ptr CNFElem -> Ptr CNF -> IO ()

-- | /nf_elem_norm_div/ /res/ /a/ /nf/ /div/ /nbits/ 
-- 
-- Set code{res} to the absolute norm of the given number field element
-- \(a\), divided by code{div} . Assumes the result to be an integer and
-- having at most code{nbits} bits.
foreign import ccall "nf_elem.h nf_elem_norm_div"
  nf_elem_norm_div :: Ptr CFmpq -> Ptr CNFElem -> Ptr CNF -> Ptr CFmpz -> CLong -> IO ()

-- | /_nf_elem_norm_div/ /rnum/ /rden/ /a/ /nf/ /divisor/ /nbits/ 
-- 
-- Set code{{rnum, rden}} to the absolute norm of the given number field
-- element \(a\), divided by code{div} . Assumes the result to be an
-- integer and having at most code{nbits} bits.
foreign import ccall "nf_elem.h _nf_elem_norm_div"
  _nf_elem_norm_div :: Ptr CFmpz -> Ptr CFmpz -> Ptr CNFElem -> Ptr CNF -> Ptr CFmpz -> CLong -> IO ()

-- | /_nf_elem_trace/ /rnum/ /rden/ /a/ /nf/ 
-- 
-- Set code{{rnum, rden}} to the absolute trace of the given number field
-- element \(a\).
foreign import ccall "nf_elem.h _nf_elem_trace"
  _nf_elem_trace :: Ptr CFmpz -> Ptr CFmpz -> Ptr CNFElem -> Ptr CNF -> IO ()

-- | /nf_elem_trace/ /res/ /a/ /nf/ 
-- 
-- Set code{res} to the absolute trace of the given number field element
-- \(a\).
foreign import ccall "nf_elem.h nf_elem_trace"
  nf_elem_trace :: Ptr CFmpq -> Ptr CNFElem -> Ptr CNF -> IO ()

-- Representation matrix -------------------------------------------------------

-- | /nf_elem_rep_mat/ /res/ /a/ /nf/ 
-- 
-- Set code{res} to the matrix representing the multiplication with \(a\)
-- with respect to the basis \(1, a, \dotsc, a^{d - 1}\), where \(a\) is
-- the generator of the number field of \(d\) is its degree.
foreign import ccall "nf_elem.h nf_elem_rep_mat"
  nf_elem_rep_mat :: Ptr CFmpqMat -> Ptr CNFElem -> Ptr CNF -> IO ()

-- | /nf_elem_rep_mat_fmpz_mat_den/ /res/ /den/ /a/ /nf/ 
-- 
-- Return a tuple \(M, d\) such that \(M/d\) is the matrix representing the
-- multiplication with \(a\) with respect to the basis
-- \(1, a, \dotsc, a^{d - 1}\), where \(a\) is the generator of the number
-- field of \(d\) is its degree. The integral matrix \(M\) is primitive.
foreign import ccall "nf_elem.h nf_elem_rep_mat_fmpz_mat_den"
  nf_elem_rep_mat_fmpz_mat_den :: Ptr CFmpzMat -> Ptr CFmpz -> Ptr CNFElem -> Ptr CNF -> IO ()

-- Modular reduction -----------------------------------------------------------

-- | /nf_elem_mod_fmpz_den/ /z/ /a/ /mod/ /nf/ 
-- 
-- If code{den == 0}, return an element \(z\) with denominator \(1\), such
-- that the coefficients of \(z - da\) are divisble by code{mod}, where
-- \(d\) is the denominator of \(a\). The coefficients of \(z\) are reduced
-- modulo code{mod}.
-- 
-- If code{den == 1}, return an element \(z\), such that \(z - a\) has
-- denominator \(1\) and the coefficients of \(z - a\) are divisble by
-- code{mod}. The coefficients of \(z\) are reduced modulo code{mod * d},
-- where \(d\) is the denominator of \(a\).
-- 
-- Reduction takes place with respect to the positive residue system.
foreign import ccall "nf_elem.h nf_elem_mod_fmpz_den"
  nf_elem_mod_fmpz_den :: Ptr CNFElem -> Ptr CNFElem -> Ptr CFmpz -> Ptr CNF -> IO ()

-- | /nf_elem_smod_fmpz_den/ /z/ /a/ /mod/ /nf/ 
-- 
-- If code{den == 0}, return an element \(z\) with denominator \(1\), such
-- that the coefficients of \(z - da\) are divisble by code{mod}, where
-- \(d\) is the denominator of \(a\). The coefficients of \(z\) are reduced
-- modulo code{mod}.
-- 
-- If code{den == 1}, return an element \(z\), such that \(z - a\) has
-- denominator \(1\) and the coefficients of \(z - a\) are divisble by
-- code{mod}. The coefficients of \(z\) are reduced modulo code{mod * d},
-- where \(d\) is the denominator of \(a\).
-- 
-- Reduction takes place with respect to the symmetric residue system.
foreign import ccall "nf_elem.h nf_elem_smod_fmpz_den"
  nf_elem_smod_fmpz_den :: Ptr CNFElem -> Ptr CNFElem -> Ptr CFmpz -> Ptr CNF -> IO ()

-- | /nf_elem_mod_fmpz/ /res/ /a/ /mod/ /nf/ 
-- 
-- Return an element \(z\) such that \(z - a\) has denominator \(1\) and
-- the coefficients of \(z - a\) are divisible by code{mod}. The
-- coefficients of \(z\) are reduced modulo code{mod * d}, where \(d\) is
-- the denominator of \(b\).
-- 
-- Reduction takes place with respect to the positive residue system.
foreign import ccall "nf_elem.h nf_elem_mod_fmpz"
  nf_elem_mod_fmpz :: Ptr CNFElem -> Ptr CNFElem -> Ptr CFmpz -> Ptr CNF -> IO ()

-- | /nf_elem_smod_fmpz/ /res/ /a/ /mod/ /nf/ 
-- 
-- Return an element \(z\) such that \(z - a\) has denominator \(1\) and
-- the coefficients of \(z - a\) are divisible by code{mod}. The
-- coefficients of \(z\) are reduced modulo code{mod * d}, where \(d\) is
-- the denominator of \(b\).
-- 
-- Reduction takes place with respect to the symmetric residue system.
foreign import ccall "nf_elem.h nf_elem_smod_fmpz"
  nf_elem_smod_fmpz :: Ptr CNFElem -> Ptr CNFElem -> Ptr CFmpz -> Ptr CNF -> IO ()

-- | /nf_elem_coprime_den/ /res/ /a/ /mod/ /nf/ 
-- 
-- Return an element \(z\) such that the denominator of \(z - a\) is
-- coprime to code{mod}.
-- 
-- Reduction takes place with respect to the positive residue system.
foreign import ccall "nf_elem.h nf_elem_coprime_den"
  nf_elem_coprime_den :: Ptr CNFElem -> Ptr CNFElem -> Ptr CFmpz -> Ptr CNF -> IO ()

-- | /nf_elem_coprime_den_signed/ /res/ /a/ /mod/ /nf/ 
-- 
-- Return an element \(z\) such that the denominator of \(z - a\) is
-- coprime to code{mod}.
-- 
-- Reduction takes place with respect to the symmetric residue system.
foreign import ccall "nf_elem.h nf_elem_coprime_den_signed"
  nf_elem_coprime_den_signed :: Ptr CNFElem -> Ptr CNFElem -> Ptr CFmpz -> Ptr CNF -> IO ()

