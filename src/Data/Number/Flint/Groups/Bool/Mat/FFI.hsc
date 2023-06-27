{-# language
    CApiFFI
  , FlexibleInstances
  , ForeignFunctionInterface
  , MultiParamTypeClasses
  , TupleSections
  , TypeFamilies
  #-}

module Data.Number.Flint.Groups.Bool.Mat.FFI (
  -- * Matrices over booleans
    BoolMat (..)
  , CBoolMat (..)
  , newBoolMat
  , withBoolMat
  , withNewBoolMat
  -- *
  -- , bool_mat_get_entry
  -- , bool_mat_set_entry
  -- * Memory management
  , bool_mat_init
  , bool_mat_clear
  , bool_mat_is_empty
  , bool_mat_is_square
  -- * Conversions
  , bool_mat_set
  -- * Input and output
  , bool_mat_print
  , bool_mat_fprint
  -- * Value comparisons
  , bool_mat_equal
  , bool_mat_any
  , bool_mat_all
  , bool_mat_is_diagonal
  , bool_mat_is_lower_triangular
  , bool_mat_is_transitive
  , bool_mat_is_nilpotent
  -- * Random generation
  , bool_mat_randtest
  , bool_mat_randtest_diagonal
  , bool_mat_randtest_nilpotent
  -- * Special matrices
  , bool_mat_zero
  , bool_mat_one
  , bool_mat_directed_path
  , bool_mat_directed_cycle
  -- * Transpose
  , bool_mat_transpose
  -- * Arithmetic
  , bool_mat_complement
  , bool_mat_add
  , bool_mat_mul
  , bool_mat_mul_entrywise
  , bool_mat_sqr
  , bool_mat_pow_ui
  -- * Special functions
  , bool_mat_trace
  , bool_mat_nilpotency_degree
  , bool_mat_transitive_closure
  , bool_mat_get_strongly_connected_components
  , bool_mat_all_pairs_longest_walk
) where 

-- Matrices over booleans ------------------------------------------------------

-- A @bool_mat_t@ represents a dense matrix over the boolean semiring
-- \(\langle \left\{0, 1\right\}, \vee, \wedge \rangle\), implemented as an
-- array of entries of type @int@.
--
-- The dimension (number of rows and columns) of a matrix is fixed at
-- initialization, and the user must ensure that inputs and outputs to an
-- operation have compatible dimensions. The number of rows or columns in a
-- matrix can be zero.
--

import System.IO.Unsafe

import Control.Monad

import Foreign.C.String
import Foreign.C.Types
import Foreign.ForeignPtr
import Foreign.Ptr ( Ptr, FunPtr, nullPtr, plusPtr )
import Foreign.Marshal.Array ( advancePtr )
import Foreign.Storable
import Foreign.Marshal ( free )

import Data.Number.Flint.Flint
import Data.Number.Flint.Fmpz
import Data.Number.Flint.Fmpz.Poly
import Data.Number.Flint.Fmpz.Mat
import Data.Number.Flint.Fmpq
import Data.Number.Flint.NMod.Types
import Data.Number.Flint.Support.D.Mat
import Data.Number.Flint.Support.Mpf.Mat

#include <flint/flint.h>
#include <flint/bool_mat.h>

--------------------------------------------------------------------------------

data BoolMat = BoolMat {-# UNPACK #-} !(ForeignPtr CBoolMat) 
data CBoolMat = CBoolMat (Ptr CInt) CLong CLong (Ptr (Ptr CInt)) 

instance Storable CBoolMat where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size bool_mat_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment bool_mat_t}
  peek = error "CBoolMat.peek: Not defined."
  poke = error "CBoolMat.poke: Not defined."
 
newBoolMat rows cols = do
  x <- mallocForeignPtr
  withForeignPtr x $ \x -> bool_mat_init x rows cols
  addForeignPtrFinalizer p_bool_mat_clear x
  return $ BoolMat x

{-# INLINE withBoolMat #-}
withBoolMat (BoolMat x) f = do
  withForeignPtr x $ \px -> f px >>= return . (BoolMat x,)

{-# INLINE withNewBoolMat #-}
withNewBoolMat rows cols f = do
  x <- newBoolMat rows cols
  withBoolMat x f
  
--------------------------------------------------------------------------------

-- | /bool_mat_get_entry/ /mat/ /i/ /j/ 
--
-- Returns the entry of matrix /mat/ at row /i/ and column /j/.
-- foreign import ccall "bool_mat.h bool_mat_get_entry"
bool_mat_get_entry :: Ptr CBoolMat -> CLong -> CLong -> IO CInt
bool_mat_get_entry mat i j = do
  CBoolMat p r c _ <- peek mat
  result <- peek (p `advancePtr` (fromIntegral (i*r + j)))
  return result
  
-- -- | /bool_mat_set_entry/ /mat/ /i/ /j/ /x/ 
-- --
-- -- Sets the entry of matrix /mat/ at row /i/ and column /j/ to /x/.
-- foreign import ccall "bool_mat.h bool_mat_set_entry"
--   bool_mat_set_entry :: Ptr CBoolMat -> CLong -> CLong -> CInt -> IO ()

-- Memory management -----------------------------------------------------------

-- | /bool_mat_init/ /mat/ /r/ /c/ 
--
-- Initializes the matrix, setting it to the zero matrix with /r/ rows and
-- /c/ columns.
foreign import ccall "bool_mat.h bool_mat_init"
  bool_mat_init :: Ptr CBoolMat -> CLong -> CLong -> IO ()

-- | /bool_mat_clear/ /mat/ 
--
-- Clears the matrix, deallocating all entries.
foreign import ccall "bool_mat.h bool_mat_clear"
  bool_mat_clear :: Ptr CBoolMat -> IO ()

foreign import ccall "bool_mat.h &bool_mat_clear"
  p_bool_mat_clear :: FunPtr (Ptr CBoolMat -> IO ())

-- | /bool_mat_is_empty/ /mat/ 
--
-- Returns nonzero iff the number of rows or the number of columns in /mat/
-- is zero. Note that this does not depend on the entry values of /mat/.
bool_mat_is_empty :: Ptr CBoolMat -> IO CInt
bool_mat_is_empty mat = do
  CBoolMat _ r c _ <- peek mat
  return $ if r == 0 || c == 0 then 1 else 0
  
-- | /bool_mat_is_square/ /mat/ 
--
-- Returns nonzero iff the number of rows is equal to the number of columns
-- in /mat/.
bool_mat_is_square :: Ptr CBoolMat -> IO CInt
bool_mat_is_square mat = do
  CBoolMat _ r c _ <- peek mat
  return $ if r == c then 1 else 0

-- Conversions -----------------------------------------------------------------

-- | /bool_mat_set/ /dest/ /src/ 
--
-- Sets /dest/ to /src/. The operands must have identical dimensions.
foreign import ccall "bool_mat.h bool_mat_set"
  bool_mat_set :: Ptr CBoolMat -> Ptr CBoolMat -> IO ()

-- Input and output ------------------------------------------------------------

-- | /bool_mat_print/ /mat/ 
--
-- Prints each entry in the matrix.
foreign import ccall "bool_mat.h bool_mat_print"
  bool_mat_print :: Ptr CBoolMat -> IO ()

-- | /bool_mat_fprint/ /file/ /mat/ 
--
-- Prints each entry in the matrix to the stream /file/.
foreign import ccall "bool_mat.h bool_mat_fprint"
  bool_mat_fprint :: Ptr CFile -> Ptr CBoolMat -> IO ()

-- Value comparisons -----------------------------------------------------------

-- | /bool_mat_equal/ /mat1/ /mat2/ 
--
-- Returns nonzero iff the matrices have the same dimensions and identical
-- entries.
foreign import ccall "bool_mat.h bool_mat_equal"
  bool_mat_equal :: Ptr CBoolMat -> Ptr CBoolMat -> IO CInt

-- | /bool_mat_any/ /mat/ 
--
-- Returns nonzero iff /mat/ has a nonzero entry.
foreign import ccall "bool_mat.h bool_mat_any"
  bool_mat_any :: Ptr CBoolMat -> IO CInt

-- | /bool_mat_all/ /mat/ 
--
-- Returns nonzero iff all entries of /mat/ are nonzero.
foreign import ccall "bool_mat.h bool_mat_all"
  bool_mat_all :: Ptr CBoolMat -> IO CInt

-- | /bool_mat_is_diagonal/ /A/ 
--
-- Returns nonzero iff \(i \ne j \implies \bar{A_{ij}}\).
foreign import ccall "bool_mat.h bool_mat_is_diagonal"
  bool_mat_is_diagonal :: Ptr CBoolMat -> IO CInt

-- | /bool_mat_is_lower_triangular/ /A/ 
--
-- Returns nonzero iff \(i < j \implies \bar{A_{ij}}\).
foreign import ccall "bool_mat.h bool_mat_is_lower_triangular"
  bool_mat_is_lower_triangular :: Ptr CBoolMat -> IO CInt

-- | /bool_mat_is_transitive/ /mat/ 
--
-- Returns nonzero iff \(A_{ij} \wedge A_{jk} \implies A_{ik}\).
foreign import ccall "bool_mat.h bool_mat_is_transitive"
  bool_mat_is_transitive :: Ptr CBoolMat -> IO CInt

-- | /bool_mat_is_nilpotent/ /A/ 
--
-- Returns nonzero iff some positive matrix power of \(A\) is zero.
foreign import ccall "bool_mat.h bool_mat_is_nilpotent"
  bool_mat_is_nilpotent :: Ptr CBoolMat -> IO CInt

-- Random generation -----------------------------------------------------------

-- | /bool_mat_randtest/ /mat/ /state/ 
--
-- Sets /mat/ to a random matrix.
foreign import ccall "bool_mat.h bool_mat_randtest"
  bool_mat_randtest :: Ptr CBoolMat -> Ptr CFRandState -> IO ()

-- | /bool_mat_randtest_diagonal/ /mat/ /state/ 
--
-- Sets /mat/ to a random diagonal matrix.
foreign import ccall "bool_mat.h bool_mat_randtest_diagonal"
  bool_mat_randtest_diagonal :: Ptr CBoolMat -> Ptr CFRandState -> IO ()

-- | /bool_mat_randtest_nilpotent/ /mat/ /state/ 
--
-- Sets /mat/ to a random nilpotent matrix.
foreign import ccall "bool_mat.h bool_mat_randtest_nilpotent"
  bool_mat_randtest_nilpotent :: Ptr CBoolMat -> Ptr CFRandState -> IO ()

-- Special matrices ------------------------------------------------------------

-- | /bool_mat_zero/ /mat/ 
--
-- Sets all entries in mat to zero.
foreign import ccall "bool_mat.h bool_mat_zero"
  bool_mat_zero :: Ptr CBoolMat -> IO ()

-- | /bool_mat_one/ /mat/ 
--
-- Sets the entries on the main diagonal to ones, and all other entries to
-- zero.
foreign import ccall "bool_mat.h bool_mat_one"
  bool_mat_one :: Ptr CBoolMat -> IO ()

-- | /bool_mat_directed_path/ /A/ 
--
-- Sets \(A_{ij}\) to \(j = i + 1\). Requires that \(A\) is a square
-- matrix.
foreign import ccall "bool_mat.h bool_mat_directed_path"
  bool_mat_directed_path :: Ptr CBoolMat -> IO ()

-- | /bool_mat_directed_cycle/ /A/ 
--
-- Sets \(A_{ij}\) to \(j = (i + 1) \mod n\) where \(n\) is the order of
-- the square matrix \(A\).
foreign import ccall "bool_mat.h bool_mat_directed_cycle"
  bool_mat_directed_cycle :: Ptr CBoolMat -> IO ()

-- Transpose -------------------------------------------------------------------

-- | /bool_mat_transpose/ /dest/ /src/ 
--
-- Sets /dest/ to the transpose of /src/. The operands must have compatible
-- dimensions. Aliasing is allowed.
foreign import ccall "bool_mat.h bool_mat_transpose"
  bool_mat_transpose :: Ptr CBoolMat -> Ptr CBoolMat -> IO ()

-- Arithmetic ------------------------------------------------------------------

-- | /bool_mat_complement/ /B/ /A/ 
--
-- Sets /B/ to the logical complement of /A/. That is \(B_{ij}\) is set to
-- \(\bar{A_{ij}}\). The operands must have the same dimensions.
foreign import ccall "bool_mat.h bool_mat_complement"
  bool_mat_complement :: Ptr CBoolMat -> Ptr CBoolMat -> IO ()

-- | /bool_mat_add/ /res/ /mat1/ /mat2/ 
--
-- Sets /res/ to the sum of /mat1/ and /mat2/. The operands must have the
-- same dimensions.
foreign import ccall "bool_mat.h bool_mat_add"
  bool_mat_add :: Ptr CBoolMat -> Ptr CBoolMat -> Ptr CBoolMat -> IO ()

-- | /bool_mat_mul/ /res/ /mat1/ /mat2/ 
--
-- Sets /res/ to the matrix product of /mat1/ and /mat2/. The operands must
-- have compatible dimensions for matrix multiplication.
foreign import ccall "bool_mat.h bool_mat_mul"
  bool_mat_mul :: Ptr CBoolMat -> Ptr CBoolMat -> Ptr CBoolMat -> IO ()

-- | /bool_mat_mul_entrywise/ /res/ /mat1/ /mat2/ 
--
-- Sets /res/ to the entrywise product of /mat1/ and /mat2/. The operands
-- must have the same dimensions.
foreign import ccall "bool_mat.h bool_mat_mul_entrywise"
  bool_mat_mul_entrywise :: Ptr CBoolMat -> Ptr CBoolMat -> Ptr CBoolMat -> IO ()

-- | /bool_mat_sqr/ /B/ /A/ 
--
-- Sets /B/ to the matrix square of /A/. The operands must both be square
-- with the same dimensions.
bool_mat_sqr :: Ptr CBoolMat -> Ptr CBoolMat -> IO ()
bool_mat_sqr b a = bool_mat_mul b a a
  
-- | /bool_mat_pow_ui/ /B/ /A/ /exp/ 
--
-- Sets /B/ to /A/ raised to the power /exp/. Requires that /A/ is a square
-- matrix.
foreign import ccall "bool_mat.h bool_mat_pow_ui"
  bool_mat_pow_ui :: Ptr CBoolMat -> Ptr CBoolMat -> CULong -> IO ()

-- Special functions -----------------------------------------------------------

-- | /bool_mat_trace/ /mat/ 
--
-- Returns the trace of the matrix, i.e. the sum of entries on the main
-- diagonal of /mat/. The matrix is required to be square. The sum is in
-- the boolean semiring, so this function returns nonzero iff any entry on
-- the diagonal of /mat/ is nonzero.
foreign import ccall "bool_mat.h bool_mat_trace"
  bool_mat_trace :: Ptr CBoolMat -> IO CInt

-- | /bool_mat_nilpotency_degree/ /A/ 
--
-- Returns the nilpotency degree of the \(n \times n\) matrix /A/. It
-- returns the smallest positive \(k\) such that \(A^k = 0\). If no such
-- \(k\) exists then the function returns \(-1\) if \(n\) is positive, and
-- otherwise it returns \(0\).
foreign import ccall "bool_mat.h bool_mat_nilpotency_degree"
  bool_mat_nilpotency_degree :: Ptr CBoolMat -> IO CLong

-- | /bool_mat_transitive_closure/ /B/ /A/ 
--
-- Sets /B/ to the transitive closure \(\sum_{k=1}^\infty A^k\). The matrix
-- /A/ is required to be square.
foreign import ccall "bool_mat.h bool_mat_transitive_closure"
  bool_mat_transitive_closure :: Ptr CBoolMat -> Ptr CBoolMat -> IO ()

-- | /bool_mat_get_strongly_connected_components/ /p/ /A/ 
--
-- Partitions the \(n\) row and column indices of the \(n \times n\) matrix
-- /A/ according to the strongly connected components (SCC) of the graph
-- for which /A/ is the adjacency matrix. If the graph has \(k\) SCCs then
-- the function returns \(k\), and for each vertex \(i \in [0, n-1]\),
-- \(p_i\) is set to the index of the SCC to which the vertex belongs. The
-- SCCs themselves can be considered as nodes in a directed acyclic graph
-- (DAG), and the SCCs are indexed in postorder with respect to that DAG.
foreign import ccall "bool_mat.h bool_mat_get_strongly_connected_components"
  bool_mat_get_strongly_connected_components :: Ptr CLong -> Ptr CBoolMat -> IO CLong

-- | /bool_mat_all_pairs_longest_walk/ /B/ /A/ 
--
-- Sets \(B_{ij}\) to the length of the longest walk with endpoint vertices
-- \(i\) and \(j\) in the graph whose adjacency matrix is /A/. The matrix
-- /A/ must be square. Empty walks with zero length which begin and end at
-- the same vertex are allowed. If \(j\) is not reachable from \(i\) then
-- no walk from \(i\) to \(j\) exists and \(B_{ij}\) is set to the special
-- value \(-1\). If arbitrarily long walks from \(i\) to \(j\) exist then
-- \(B_{ij}\) is set to the special value \(-2\).
-- 
-- The function returns \(-2\) if any entry of \(B_{ij}\) is \(-2\), and
-- otherwise it returns the maximum entry in \(B\), except if \(A\) is
-- empty in which case \(-1\) is returned. Note that the returned value is
-- one less than that of @nilpotency_degree@.
-- 
-- This function can help quantify entrywise errors in a truncated
-- evaluation of a matrix power series. If /A/ is an indicator matrix with
-- the same sparsity pattern as a matrix \(M\) over the real or complex
-- numbers, and if \(B_{ij}\) does not take the special value \(-2\), then
-- the tail \(\left[ \sum_{k=N}^\infty a_k M^k \right]_{ij}\) vanishes when
-- \(N > B_{ij}\).
foreign import ccall "bool_mat.h bool_mat_all_pairs_longest_walk"
  bool_mat_all_pairs_longest_walk :: Ptr CFmpzMat -> Ptr CBoolMat -> IO CLong

