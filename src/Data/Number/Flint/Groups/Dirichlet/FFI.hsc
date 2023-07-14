module Data.Number.Flint.Groups.Dirichlet.FFI (
  -- * Dirichlet characters
  -- * Multiplicative group modulo /q/
    DirichletGroup (..)
  , CDirichletGroup (..)
  , newDirichletGroup
  , withDirichletGroup
  , withNewDirichletGroup
  , dirichlet_group_init
  , dirichlet_subgroup_init
  , dirichlet_group_clear
  , dirichlet_group_size
  , dirichlet_group_num_primitive
  , dirichlet_group_dlog_precompute
  , dirichlet_group_dlog_clear
  -- * Character type
  , DirichletChar (..)
  , CDirichletChar (..)
  , newDirichletChar 
  , withDirichletChar
  , withNewDirichletChar
  , dirichlet_char_init
  , dirichlet_char_clear
  , dirichlet_char_print
  , dirichlet_char_log
  , dirichlet_char_exp
  , _dirichlet_char_exp
  , dirichlet_char_one
  , dirichlet_char_first_primitive
  , dirichlet_char_set
  , dirichlet_char_next
  , dirichlet_char_next_primitive
  , dirichlet_index_char
  , dirichlet_char_index
  , dirichlet_char_eq
  , dirichlet_char_eq_deep
  -- * Character properties
  , dirichlet_char_is_principal
  , dirichlet_conductor_ui
  , dirichlet_conductor_char
  , dirichlet_parity_ui
  , dirichlet_parity_char
  , dirichlet_order_ui
  , dirichlet_order_char
  , dirichlet_char_is_real
  , dirichlet_char_is_primitive
  -- * Character evaluation
  , dirichlet_pairing
  , dirichlet_pairing_char
  , dirichlet_chi
  , dirichlet_chi_vec
  , dirichlet_chi_vec_order
  -- * Character operations
  , dirichlet_char_mul
  , dirichlet_char_pow
  , dirichlet_char_lift
  , dirichlet_char_lower
) where

-- Dirichlet characters --------------------------------------------------------

import Foreign.C.Types
import Foreign.Ptr
import Foreign.ForeignPtr
import Foreign.Storable

#include <flint/dirichlet.h>

-- dirichlet_group_t -----------------------------------------------------------

data DirichletGroup =
  DirichletGroup {-# UNPACK #-} !(ForeignPtr CDirichletGroup)
data CDirichletGroup = CFlint DirichletGroup

newDirichletGroup n = do
  x <- mallocForeignPtr
  withForeignPtr x $ \x -> do
    dirichlet_group_init x (fromIntegral n)
  addForeignPtrFinalizer p_dirichlet_group_clear x
  return $ DirichletGroup x

-- | Use DirichletGroup in `f`.
{-# INLINE withDirichletGroup #-}
withDirichletGroup (DirichletGroup p) f = do
  withForeignPtr p $ \fp -> (DirichletGroup p,) <$> f fp

-- | Apply `f` to new DirichletGroup.
{-# INLINE withNewDirichletGroup #-}
withNewDirichletGroup n f = do
  x <- newDirichletGroup n
  withDirichletGroup x f

instance Storable CDirichletGroup where
  {-# INLINE sizeOf #-}
  sizeOf    _ = #{size      dirichlet_group_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment dirichlet_group_t}
  peek = undefined
  poke = undefined

-- Multiplicative group modulo /q/ ---------------------------------------------

-- | /dirichlet_group_init/ /G/ /q/ 
-- 
-- Initializes /G/ to the group of Dirichlet characters mod /q/.
-- 
-- This method computes a canonical decomposition of /G/ in terms of cyclic
-- groups, which are the mod \(p^e\) subgroups for \(p^e\|q\), plus the
-- specific generator described by Conrey for each subgroup.
-- 
-- In particular /G/ contains:
-- 
-- -   the number /num/ of components
-- -   the generators
-- -   the exponent /expo/ of the group
-- 
-- It does /not/ automatically precompute lookup tables of discrete
-- logarithms or numerical roots of unity, and can therefore safely be
-- called even with large /q/.
-- 
-- For implementation reasons, the largest prime factor of /q/ must not
-- exceed \(10^{16}\). This restriction could be removed in the future. The
-- function returns 1 on success and 0 if a factor is too large.
foreign import ccall "dirichlet.h dirichlet_group_init"
  dirichlet_group_init :: Ptr CDirichletGroup -> CULong -> IO CInt

-- | /dirichlet_subgroup_init/ /H/ /G/ /h/ 
-- 
-- Given an already computed group /G/ mod \(q\), initialize its subgroup
-- /H/ defined mod \(h\mid q\). Precomputed discrete log tables are
-- inherited.
foreign import ccall "dirichlet.h dirichlet_subgroup_init"
  dirichlet_subgroup_init :: Ptr CDirichletGroup -> Ptr CDirichletGroup -> CULong -> IO ()

-- | /dirichlet_group_clear/ /G/ 
-- 
-- Clears /G/. Remark this function does /not/ clear the discrete logarithm
-- tables stored in /G/ (which may be shared with another group).
foreign import ccall "dirichlet.h dirichlet_group_clear"
  dirichlet_group_clear :: Ptr CDirichletGroup -> IO ()

foreign import ccall "dirichlet.h &dirichlet_group_clear"
  p_dirichlet_group_clear :: FunPtr (Ptr CDirichletGroup -> IO ())

-- | /dirichlet_group_size/ /G/ 
-- 
-- Returns the number of elements in /G/, i.e. \(\varphi(q)\).
foreign import ccall "dirichlet.h dirichlet_group_size"
  dirichlet_group_size :: Ptr CDirichletGroup -> IO CULong

-- | /dirichlet_group_num_primitive/ /G/ 
-- 
-- Returns the number of primitive elements in /G/.
foreign import ccall "dirichlet.h dirichlet_group_num_primitive"
  dirichlet_group_num_primitive :: Ptr CDirichletGroup -> IO CULong

-- | /dirichlet_group_dlog_precompute/ /G/ /num/ 
-- 
-- Precompute decomposition and tables for discrete log computations in
-- /G/, so as to minimize the complexity of /num/ calls to discrete
-- logarithms.
-- 
-- If /num/ gets very large, the entire group may be indexed.
foreign import ccall "dirichlet.h dirichlet_group_dlog_precompute"
  dirichlet_group_dlog_precompute :: Ptr CDirichletGroup -> CULong -> IO ()

-- | /dirichlet_group_dlog_clear/ /G/ /num/ 
-- 
-- Clear discrete logarithm tables in /G/. When discrete logarithm tables
-- are shared with subgroups, those subgroups must be cleared before
-- clearing the tables.
foreign import ccall "dirichlet.h dirichlet_group_dlog_clear"
  dirichlet_group_dlog_clear :: Ptr CDirichletGroup -> CULong -> IO ()

-- Character type --------------------------------------------------------------

data DirichletChar = DirichletChar {-# UNPACK #-} !(ForeignPtr CDirichletChar)
data CDirichletChar = CDirichletChar CULong (Ptr CULong)

newDirichletChar group = do
  x <- mallocForeignPtr
  withForeignPtr x $ \x -> do
    dirichlet_char_init x group
  addForeignPtrFinalizer p_dirichlet_char_clear x
  return $ DirichletChar x

-- | Use DirichletChar in `f`.
{-# INLINE withDirichletChar #-}
withDirichletChar (DirichletChar p) f = do
  withForeignPtr p $ \fp -> (DirichletChar p,) <$> f fp

-- | Apply `f` to new DirichletChar.
{-# INLINE withNewDirichletChar #-}
withNewDirichletChar group f = do
  x <- newDirichletChar group
  withDirichletChar x f

instance Storable CDirichletChar where
  {-# INLINE sizeOf #-}
  sizeOf    _ = #{size      dirichlet_char_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment dirichlet_char_t}
  peek ptr = CDirichletChar
    <$> #{peek dirichlet_char_struct, n  } ptr
    <*> #{peek dirichlet_char_struct, log} ptr
  poke ptr (CDirichletChar n log) = do
    #{poke dirichlet_char_struct, n    } ptr n
    #{poke dirichlet_char_struct, log  } ptr log

--------------------------------------------------------------------------------

-- | /dirichlet_char_init/ /chi/ /G/ 
-- 
-- Initializes /chi/ to an element of the group /G/ and sets its value to
-- the principal character.
foreign import ccall "dirichlet.h dirichlet_char_init"
  dirichlet_char_init :: Ptr CDirichletChar -> Ptr CDirichletGroup -> IO ()

-- | /dirichlet_char_clear/ /chi/ 
-- 
-- Clears /chi/.
foreign import ccall "dirichlet.h dirichlet_char_clear"
  dirichlet_char_clear :: Ptr CDirichletChar -> IO ()

foreign import ccall "dirichlet.h &dirichlet_char_clear"
  p_dirichlet_char_clear :: FunPtr (Ptr CDirichletChar -> IO ())

-- | /dirichlet_char_print/ /G/ /chi/ 
-- 
-- Prints the array of exponents representing this character.
foreign import ccall "dirichlet.h dirichlet_char_print"
  dirichlet_char_print :: Ptr CDirichletGroup -> Ptr CDirichletChar -> IO ()

-- | /dirichlet_char_log/ /x/ /G/ /m/ 
-- 
-- Sets /x/ to the character of number /m/, computing its log using
-- discrete logarithm in /G/.
foreign import ccall "dirichlet.h dirichlet_char_log"
  dirichlet_char_log :: Ptr CDirichletChar -> Ptr CDirichletGroup -> CULong -> IO ()

-- | /dirichlet_char_exp/ /G/ /x/ 
-- 
-- Returns the number /m/ corresponding to exponents in /x/.
foreign import ccall "dirichlet.h dirichlet_char_exp"
  dirichlet_char_exp :: Ptr CDirichletGroup -> Ptr CDirichletChar -> IO CULong

-- | /_dirichlet_char_exp/ /x/ /G/ 
-- 
-- Computes and returns the number /m/ corresponding to exponents in /x/.
-- This function is for internal use.
foreign import ccall "dirichlet.h _dirichlet_char_exp"
  _dirichlet_char_exp :: Ptr CDirichletChar -> Ptr CDirichletGroup -> IO CULong

-- | /dirichlet_char_one/ /x/ /G/ 
-- 
-- Sets /x/ to the principal character in /G/, having /log/
-- \([0,\dots 0]\).
foreign import ccall "dirichlet.h dirichlet_char_one"
  dirichlet_char_one :: Ptr CDirichletChar -> Ptr CDirichletGroup -> IO ()

-- | /dirichlet_char_first_primitive/ /x/ /G/ 
-- 
-- Sets /x/ to the first primitive character of /G/, having /log/
-- \([1,\dots 1]\), or \([0, 1, \dots 1]\) if \(8\mid q\).
foreign import ccall "dirichlet.h dirichlet_char_first_primitive"
  dirichlet_char_first_primitive :: Ptr CDirichletChar -> Ptr CDirichletGroup -> IO ()

-- | /dirichlet_char_set/ /x/ /G/ /y/ 
-- 
-- Sets /x/ to the element /y/.
foreign import ccall "dirichlet.h dirichlet_char_set"
  dirichlet_char_set :: Ptr CDirichletChar -> Ptr CDirichletGroup -> Ptr CDirichletChar -> IO ()

-- | /dirichlet_char_next/ /x/ /G/ 
-- 
-- Sets /x/ to the next character in /G/ according to lexicographic
-- ordering of /log/.
-- 
-- The return value is the index of the last updated exponent of /x/, or
-- /-1/ if the last element has been reached.
-- 
-- This function allows to iterate on all elements of /G/ looping on their
-- /log/. Note that it produces elements in seemingly random /number/
-- order.
-- 
-- The following template can be used for such a loop:
-- 
-- > dirichlet_char_one(chi, G);
-- > do {
-- >     /* use character chi */
-- > } while (dirichlet_char_next(chi, G) >= 0);
foreign import ccall "dirichlet.h dirichlet_char_next"
  dirichlet_char_next :: Ptr CDirichletChar -> Ptr CDirichletGroup -> IO CInt

-- | /dirichlet_char_next_primitive/ /x/ /G/ 
-- 
-- Same as @dirichlet_char_next@, but jumps to the next primitive character
-- of /G/.
foreign import ccall "dirichlet.h dirichlet_char_next_primitive"
  dirichlet_char_next_primitive :: Ptr CDirichletChar -> Ptr CDirichletGroup -> IO CInt

-- | /dirichlet_index_char/ /G/ /x/ 
-- 
-- Returns the lexicographic index of the /log/ of /x/ as an integer in
-- \(0\dots \varphi(q)\).
foreign import ccall "dirichlet.h dirichlet_index_char"
  dirichlet_index_char :: Ptr CDirichletGroup -> Ptr CDirichletChar -> IO CULong

-- | /dirichlet_char_index/ /x/ /G/ /j/ 
-- 
-- Sets /x/ to the character whose /log/ has lexicographic index /j/.
foreign import ccall "dirichlet.h dirichlet_char_index"
  dirichlet_char_index :: Ptr CDirichletChar -> Ptr CDirichletGroup -> CULong -> IO ()

foreign import ccall "dirichlet.h dirichlet_char_eq"
  dirichlet_char_eq :: Ptr CDirichletChar -> Ptr CDirichletChar -> IO CInt

-- | /dirichlet_char_eq_deep/ /G/ /x/ /y/ 
-- 
-- Return 1 if /x/ equals /y/.
-- 
-- The second version checks every byte of the representation and is
-- intended for testing only.
foreign import ccall "dirichlet.h dirichlet_char_eq_deep"
  dirichlet_char_eq_deep :: Ptr CDirichletGroup -> Ptr CDirichletChar -> Ptr CDirichletChar -> IO CInt

-- Character properties --------------------------------------------------------

-- As a consequence of the Conrey numbering, all these numbers are
-- available at the level of /number/ and /char/ object. Both case require
-- no discrete log computation.
--
-- | /dirichlet_char_is_principal/ /G/ /chi/ 
-- 
-- Returns 1 if /chi/ is the principal character mod /q/.
foreign import ccall "dirichlet.h dirichlet_char_is_principal"
  dirichlet_char_is_principal :: Ptr CDirichletGroup -> Ptr CDirichletChar -> IO CInt

foreign import ccall "dirichlet.h dirichlet_conductor_ui"
  dirichlet_conductor_ui :: Ptr CDirichletGroup -> CULong -> IO CULong

-- | /dirichlet_conductor_char/ /G/ /x/ 
-- 
-- Returns the /conductor/ of \(\chi_q(a,\cdot)\), that is the smallest
-- \(r\) dividing \(q\) such \(\chi_q(a,\cdot)\) can be obtained as a
-- character mod \(r\).
foreign import ccall "dirichlet.h dirichlet_conductor_char"
  dirichlet_conductor_char :: Ptr CDirichletGroup -> Ptr CDirichletChar -> IO CULong

foreign import ccall "dirichlet.h dirichlet_parity_ui"
  dirichlet_parity_ui :: Ptr CDirichletGroup -> CULong -> IO CInt

-- | /dirichlet_parity_char/ /G/ /x/ 
-- 
-- Returns the /parity/ \(\lambda\) in \(\{0,1\}\) of \(\chi_q(a,\cdot)\),
-- such that \(\chi_q(a,-1)=(-1)^\lambda\).
foreign import ccall "dirichlet.h dirichlet_parity_char"
  dirichlet_parity_char :: Ptr CDirichletGroup -> Ptr CDirichletChar -> IO CInt

foreign import ccall "dirichlet.h dirichlet_order_ui"
  dirichlet_order_ui :: Ptr CDirichletGroup -> CULong -> IO CULong

-- | /dirichlet_order_char/ /G/ /x/ 
-- 
-- Returns the order of \(\chi_q(a,\cdot)\) which is the order of
-- \(a\bmod q\).
foreign import ccall "dirichlet.h dirichlet_order_char"
  dirichlet_order_char :: Ptr CDirichletGroup -> Ptr CDirichletChar -> IO CULong

-- | /dirichlet_char_is_real/ /G/ /chi/ 
-- 
-- Returns 1 if /chi/ is a real character (iff it has order \(\leq 2\)).
foreign import ccall "dirichlet.h dirichlet_char_is_real"
  dirichlet_char_is_real :: Ptr CDirichletGroup -> Ptr CDirichletChar -> IO CInt

-- | /dirichlet_char_is_primitive/ /G/ /chi/ 
-- 
-- Returns 1 if /chi/ is primitive (iff its conductor is exactly /q/).
foreign import ccall "dirichlet.h dirichlet_char_is_primitive"
  dirichlet_char_is_primitive :: Ptr CDirichletGroup -> Ptr CDirichletChar -> IO CInt

-- Character evaluation --------------------------------------------------------

-- Dirichlet characters take value in a finite cyclic group of roots of
-- unity plus zero.
--
-- Evaluation functions return a /ulong/, this number corresponds to the
-- power of a primitive root of unity, the special value
-- /DIRICHLET_CHI_NULL/ encoding the zero value.
--
foreign import ccall "dirichlet.h dirichlet_pairing"
  dirichlet_pairing :: Ptr CDirichletGroup -> CULong -> CULong -> IO CULong

-- | /dirichlet_pairing_char/ /G/ /chi/ /psi/ 
-- 
-- Compute the value of the Dirichlet pairing on numbers /m/ and /n/, as
-- exponent modulo /G->expo/.
-- 
-- The /char/ variant takes as input two characters, so that no discrete
-- logarithm is computed.
-- 
-- The returned value is the numerator of the actual value exponent mod the
-- group exponent /G->expo/.
foreign import ccall "dirichlet.h dirichlet_pairing_char"
  dirichlet_pairing_char :: Ptr CDirichletGroup -> Ptr CDirichletChar -> Ptr CDirichletChar -> IO CULong

-- | /dirichlet_chi/ /G/ /chi/ /n/ 
-- 
-- Compute the value \(\chi(n)\) as the exponent modulo /G->expo/.
foreign import ccall "dirichlet.h dirichlet_chi"
  dirichlet_chi :: Ptr CDirichletGroup -> Ptr CDirichletChar -> CULong -> IO CULong

-- | /dirichlet_chi_vec/ /v/ /G/ /chi/ /nv/ 
-- 
-- Compute the list of exponent values /v[k]/ for \(0\leq k < nv\), as
-- exponents modulo /G->expo/.
foreign import ccall "dirichlet.h dirichlet_chi_vec"
  dirichlet_chi_vec :: Ptr CULong -> Ptr CDirichletGroup -> Ptr CDirichletChar -> CLong -> IO ()

-- | /dirichlet_chi_vec_order/ /v/ /G/ /chi/ /order/ /nv/ 
-- 
-- Compute the list of exponent values /v[k]/ for \(0\leq k < nv\), as
-- exponents modulo /order/, which is assumed to be a multiple of the order
-- of /chi/.
foreign import ccall "dirichlet.h dirichlet_chi_vec_order"
  dirichlet_chi_vec_order :: Ptr CULong -> Ptr CDirichletGroup -> Ptr CDirichletChar -> CULong -> CLong -> IO ()

-- Character operations --------------------------------------------------------

-- | /dirichlet_char_mul/ /chi12/ /G/ /chi1/ /chi2/ 
-- 
-- Multiply two characters of the same group /G/.
foreign import ccall "dirichlet.h dirichlet_char_mul"
  dirichlet_char_mul :: Ptr CDirichletChar -> Ptr CDirichletGroup -> Ptr CDirichletChar -> Ptr CDirichletChar -> IO ()

-- | /dirichlet_char_pow/ /c/ /G/ /a/ /n/ 
-- 
-- Take the power of a character.
foreign import ccall "dirichlet.h dirichlet_char_pow"
  dirichlet_char_pow :: Ptr CDirichletChar -> Ptr CDirichletGroup -> Ptr CDirichletChar -> CULong -> IO ()

-- | /dirichlet_char_lift/ /chi_G/ /G/ /chi_H/ /H/ 
-- 
-- If /H/ is a subgroup of /G/, computes the character in /G/ corresponding
-- to /chi_H/ in /H/.
foreign import ccall "dirichlet.h dirichlet_char_lift"
  dirichlet_char_lift :: Ptr CDirichletChar -> Ptr CDirichletGroup -> Ptr CDirichletChar -> Ptr CDirichletGroup -> IO ()

-- | /dirichlet_char_lower/ /chi_H/ /H/ /chi_G/ /G/ 
-- 
-- If /chi_G/ is a character of /G/ which factors through /H/, sets /chi_H/
-- to the corresponding restriction in /H/.
-- 
-- This requires \(c(\chi_G)\mid q_H\mid q_G\), where \(c(\chi_G)\) is the
-- conductor of \(\chi_G\) and \(q_G, q_H\) are the moduli of G and H.
foreign import ccall "dirichlet.h dirichlet_char_lower"
  dirichlet_char_lower :: Ptr CDirichletChar -> Ptr CDirichletGroup -> Ptr CDirichletChar -> Ptr CDirichletGroup -> IO ()

