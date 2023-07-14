{-|
module      :  Data.Number.Flint.QSieve.FFI
copyright   :  (c) 2022 Hartmut Monien
license     :  GNU GPL, version 2 or above (see LICENSE)
maintainer  :  hmonien@uni-bonn.de
-}
module Data.Number.Flint.QSieve.FFI (
  -- * Quadratic sieve
    Qs (..)
  , CQs()
  , newQs
  , withQs
  -- *
  , qsieve_knuth_schroeppel
  , qsieve_primes_init
  , qsieve_primes_increment
  , qsieve_init_A
  , qsieve_next_A
  --, qsieve_compute_pre_data
  , qsieve_init_poly_first
  , qsieve_init_poly_next
  , qsieve_compute_C
  , qsieve_do_sieving
  , qsieve_do_sieving2
  , qsieve_evaluate_candidate
  , qsieve_evaluate_sieve
  , qsieve_collect_relations
  , qsieve_write_to_file
  , qsieve_get_table_entry
  , qsieve_add_to_hashtable
  , qsieve_parse_relation
  , qsieve_merge_relation
  , qsieve_compare_relation
  , qsieve_remove_duplicates
  --, qsieve_insert_relation2
  , qsieve_process_relation
  , qsieve_factor
) where

-- Quadratic sieve -------------------------------------------------------------

import Control.Monad

import Foreign.C.String
import Foreign.C.Types
import Foreign.ForeignPtr
import Foreign.Ptr ( Ptr, FunPtr, plusPtr )
import Foreign.Storable
import Foreign.Marshal ( free )

import Data.Number.Flint.Flint
import Data.Number.Flint.Fmpz
import Data.Number.Flint.Fmpz.Factor

#include <flint/flint.h>
#include <flint/fmpz.h>
#include <flint/qsieve.h>

-- qs_t ------------------------------------------------------------------------

data Qs = Qs {-# UNPACK #-} !(ForeignPtr CQs)
type CQs = CFlint Qs

instance Storable CQs where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size qs_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment qs_t}
  peek = undefined
  poke = undefined

newQs n = do
  x <- mallocForeignPtr
  withForeignPtr x $ \x ->
    withFmpz n $ \n -> do
      qsieve_init x n
  addForeignPtrFinalizer p_qsieve_clear x
  return $ Qs x

{-# INLINE withQs #-}
withQs (Qs x) f = do
  withForeignPtr x $ \px -> f px >>= return . (Qs x,)

-- hash_t ----------------------------------------------------------------------

data Hash = Hash {-# UNPACK #-} !(ForeignPtr CHash)
data CHash = CHash CMpLimb CMpLimb CMpLimb

instance Storable CHash where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size hash_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment hash_t}
  peek ptr = CHash
    <$> #{peek hash_t, prime} ptr
    <*> #{peek hash_t, next } ptr
    <*> #{peek hash_t, count} ptr 
  poke ptr (CHash prime next count) = do
    #{poke hash_t, prime} ptr prime
    #{poke hash_t, next } ptr next
    #{poke hash_t, count} ptr count
    
-- relation_t ------------------------------------------------------------------

data Relation = Relation {-# UNPACK #-} !(ForeignPtr CRelation)
data CRelation = CRelation CMpLimb CLong CLong (Ptr CLong) (Ptr CFac) (Ptr CFmpz)

instance Storable CRelation where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size relation_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment relation_t}
  peek ptr = CRelation
    <$> #{peek relation_t, lp          } ptr
    <*> #{peek relation_t, num_factors } ptr
    <*> #{peek relation_t, small_primes} ptr
    <*> #{peek relation_t, small       } ptr
    <*> #{peek relation_t, factor      } ptr
    <*> #{peek relation_t, Y           } ptr
  poke ptr (CRelation lp num_factors small_primes small factor y) = do
    #{poke relation_t, lp          } ptr lp 
    #{poke relation_t, num_factors } ptr num_factors
    #{poke relation_t, small_primes} ptr small_primes
    #{poke relation_t, small       } ptr small
    #{poke relation_t, factor      } ptr factor
    #{poke relation_t, Y           } ptr y

-- fac_t -----------------------------------------------------------------------

data Fac = Fac {-# UNPACK #-} !(ForeignPtr CFac)
data CFac = CFac CLong CLong

instance Storable CFac where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size fac_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment fac_t}
  peek ptr = CFac
    <$> #{peek fac_t, ind} ptr
    <*> #{peek fac_t, exp} ptr
  poke ptr (CFac ind exp) = do
    #{poke fac_t, ind} ptr ind
    #{poke fac_t, ind} ptr exp

--------------------------------------------------------------------------------

foreign import ccall "flint/qsieve.h qsieve_init"
  qsieve_init :: Ptr CQs -> Ptr CFmpz -> IO ()
  
foreign import ccall "flint/qsieve.h qsieve_clear"
  qsieve_clear :: Ptr CQs -> IO ()

foreign import ccall "flint/qsieve.h &qsieve_clear"
  p_qsieve_clear :: FunPtr (Ptr CQs -> IO ())

--------------------------------------------------------------------------------

-- | /qsieve_knuth_schroeppel/ /qs_inf/ 
--
-- Return the Knuth-Schroeppel multiplier for the \(n\), integer to be
-- factored based upon the Knuth-Schroeppel function.
foreign import ccall "qsieve.h qsieve_knuth_schroeppel"
  qsieve_knuth_schroeppel :: Ptr CQs -> IO CMpLimb

-- | /qsieve_primes_init/ /qs_inf/ 
--
-- Compute the factor base prime along with there inverse for \(kn\), where
-- \(k\) is Knuth-Schroeppel multiplier and \(n\) is the integer to be
-- factored. It also computes the square root of \(kn\) modulo factor base
-- primes.
foreign import ccall "qsieve.h qsieve_primes_init"
  qsieve_primes_init :: Ptr CQs -> IO CMpLimb

-- | /qsieve_primes_increment/ /qs_inf/ /delta/ 
--
-- It increase the number of factor base primes by amount \'delta\' and
-- calculate inverse of those primes along with the square root of \(kn\)
-- modulo those primes.
foreign import ccall "qsieve.h qsieve_primes_increment"
  qsieve_primes_increment :: Ptr CQs -> CMpLimb -> IO CMpLimb

-- | /qsieve_init_A0/ /qs_inf/ 
--
-- First it chooses the possible range of factor of \(A _0\), based on the
-- number of bits in optimal value of \(A _0\). It tries to select range
-- such that we have plenty of primes to choose from as well as number of
-- factor in \(A _0\) are sufficient. For input of size less than 130 bit,
-- this selection method doesn\'t work therefore we randomly generate 2 or
-- 3-subset of all the factor base prime as the factor of \(A _0\).
-- Otherwise, if we have to select \(s\) factor for \(A _0\), we generate
-- \(s - 1\)-subset from odd indices of the possible range of factor and
-- then search last factor using binary search from the even indices of
-- possible range of factor such that value of \(A _0\) is close to it\'s
-- optimal value.
foreign import ccall "qsieve.h qsieve_init_A"
  qsieve_init_A :: Ptr CQs -> IO ()

-- | /qsieve_next_A0/ /qs_inf/ 
--
-- Find next candidate for \(A _0\) as follows: generate next lexicographic
-- \(s - 1\)-subset from the odd indices of possible range of factor base
-- and choose the last factor from even indices using binary search so that
-- value \(A _0\) is close to it\'s optimal value.
foreign import ccall "qsieve.h qsieve_next_A"
  qsieve_next_A :: Ptr CQs -> IO ()

-- -- | /qsieve_compute_pre_data/ /qs_inf/ 
-- --
-- -- Precompute all the data associated with factor\'s of \(A _0\), since
-- -- \(A _0\) is going to be fixed for several \(A\).
-- foreign import ccall "qsieve.h qsieve_compute_pre_data"
--   qsieve_compute_pre_data :: Ptr CQs -> IO ()

-- | /qsieve_init_poly_first/ /qs_inf/ 
--
-- Initializes the value of \(A = q _0 * A _0\), where \(q _0\) is
-- non-factor base prime. precompute the data necessary for generating
-- different \(B\) value using grey code formula. Combine the data
-- calculated for the factor of \(A _0\) along with the parameter \(q _0\)
-- to obtain data as for factor of \(A\). It also calculates the sieve
-- offset for all the factor base prime, for first polynomial.
foreign import ccall "qsieve.h qsieve_init_poly_first"
  qsieve_init_poly_first :: Ptr CQs -> IO ()

-- | /qsieve_init_poly_next/ /qs_inf/ 
--
-- Generate next polynomial or next \(B\) value for particular \(A\) and
-- also updates the sieve offsets for all the factor base prime, for this
-- \(B\) value.
foreign import ccall "qsieve.h qsieve_init_poly_next"
  qsieve_init_poly_next :: Ptr CQs -> IO ()

-- | /qsieve_compute_C/ /qs_inf/ 
--
-- Given \(A\) and \(B\), calculate \(C = (B ^2 - A) / N\).
foreign import ccall "qsieve.h qsieve_compute_C"
  qsieve_compute_C :: Ptr CQs -> IO ()

-- | /qsieve_do_sieving/ /qs_inf/ /sieve/ 
--
-- First initialize the sieve array to zero, then for each \(p \in\)
-- @factor base@, add \(\log_2(p)\) to the locations
-- \(\operatorname{soln1} _p + i * p\) and
-- \(\operatorname{soln2} _p + i * p\) for \(i = 0, 1, 2,\dots\), where
-- \(\operatorname{soln1} _p\) and \(\operatorname{soln2} _p\) are the
-- sieve offsets calculated for \(p\).
foreign import ccall "qsieve.h qsieve_do_sieving"
  qsieve_do_sieving :: Ptr CQs -> CString -> IO ()

-- | /qsieve_do_sieving2/ /qs_inf/ 
--
-- Perform the same task as above but instead of sieving over whole array
-- at once divide the array in blocks and then sieve over each block for
-- all the primes in factor base.
foreign import ccall "qsieve.h qsieve_do_sieving2"
  qsieve_do_sieving2 :: Ptr CQs -> IO ()

-- | /qsieve_evaluate_candidate/ /qs_inf/ /i/ /sieve/ 
--
-- For location \(i\) in sieve array value at which, is greater than sieve
-- threshold, check the value of \(Q(x)\) at position \(i\) for smoothness.
-- If value is found to be smooth then store it for later processing, else
-- check the residue for the partial if it is found to be partial then
-- store it for late processing.
foreign import ccall "qsieve.h qsieve_evaluate_candidate"
  qsieve_evaluate_candidate :: Ptr CQs -> CLong -> CString -> IO CLong

-- | /qsieve_evaluate_sieve/ /qs_inf/ /sieve/ 
--
-- Scan the sieve array for location at, which accumulated value is greater
-- than sieve threshold.
foreign import ccall "qsieve.h qsieve_evaluate_sieve"
  qsieve_evaluate_sieve :: Ptr CQs -> CString -> IO CLong

-- | /qsieve_collect_relations/ /qs_inf/ /sieve/ 
--
-- Call for initialization of polynomial, sieving, and scanning of sieve
-- for all the possible polynomials for particular hypercube i.e. \(A\).
foreign import ccall "qsieve.h qsieve_collect_relations"
  qsieve_collect_relations :: Ptr CQs -> CString -> IO CLong

-- | /qsieve_write_to_file/ /qs_inf/ /prime/ /Y/ 
--
-- Write a relation to the file. Format is as follows, first write large
-- prime, in case of full relation it is 1, then write exponent of small
-- primes, then write number of factor followed by offset of factor in
-- factor base and their exponent and at last value of \(Q(x)\) for
-- particular relation. each relation is written in new line.
foreign import ccall "qsieve.h qsieve_write_to_file"
  qsieve_write_to_file :: Ptr CQs -> CMpLimb -> Ptr CFmpz -> IO ()

-- | /qsieve_get_table_entry/ /qs_inf/ /prime/ 
--
-- Return the pointer to the location of \'prime\' is hash table if it
-- exist, else create and entry for it in hash table and return pointer to
-- that.
foreign import ccall "qsieve.h qsieve_get_table_entry"
  qsieve_get_table_entry :: Ptr CQs -> CMpLimb -> IO (Ptr (Ptr CHash))

-- | /qsieve_add_to_hashtable/ /qs_inf/ /prime/ 
--
-- Add \'prime\' to the hast table.
foreign import ccall "qsieve.h qsieve_add_to_hashtable"
  qsieve_add_to_hashtable :: Ptr CQs -> CMpLimb -> IO ()

-- | /qsieve_parse_relation/ /qs_inf/ /str/ 
--
-- Given a string representation of relation from the file, parse it to
-- obtain all the parameters of relation.
foreign import ccall "qsieve.h qsieve_parse_relation"
  qsieve_parse_relation :: Ptr CQs -> CString -> IO (Ptr CRelation)

-- | /qsieve_merge_relation/ /qs_inf/ /a/ /b/ 
--
-- Given two partial relation having same large prime, merge them to obtain
-- a full relation.
foreign import ccall "qsieve.h qsieve_merge_relation"
  qsieve_merge_relation :: Ptr CQs -> Ptr CRelation -> Ptr CRelation -> IO (Ptr CRelation)

-- | /qsieve_compare_relation/ /a/ /b/ 
--
-- Compare two relation based on, first large prime, then number of factor
-- and then offsets of factor in factor base.
foreign import ccall "qsieve.h qsieve_compare_relation"
  qsieve_compare_relation :: Ptr ()  -> Ptr ()  -> IO CInt

-- | /qsieve_remove_duplicates/ /rel_list/ /num_relations/ 
--
-- Remove duplicate from given list of relations by sorting relations in
-- the list.
foreign import ccall "qsieve.h qsieve_remove_duplicates"
  qsieve_remove_duplicates :: Ptr (Ptr CRelation) -> CLong -> IO CInt

-- -- | /qsieve_insert_relation2/ /qs_inf/ /rel_list/ /num_relations/ 
-- --
-- -- Given a list of relations, insert each relation from the list into the
-- -- matrix for further processing.
-- foreign import ccall "qsieve.h qsieve_insert_relation2"
--   qsieve_insert_relation2 :: Ptr CQs -> Ptr (Ptr CRelation) -> CLong -> IO ()

-- | /qsieve_process_relation/ /qs_inf/ 
--
-- After we have accumulated required number of relations, first process
-- the file by reading all the relations, removes singleton. Then merge all
-- the possible partial to obtain full relations.
foreign import ccall "qsieve.h qsieve_process_relation"
  qsieve_process_relation :: Ptr CQs -> IO ()

-- | /qsieve_factor/ /factors/ /n/ 
--
-- Factor \(n\) using the quadratic sieve method. It is required that \(n\)
-- is not a prime and not a perfect power. There is no guarantee that the
-- factors found will be prime, or distinct.
foreign import ccall "qsieve.h qsieve_factor"
  qsieve_factor :: Ptr CFmpzFactor -> Ptr CFmpz -> IO ()

