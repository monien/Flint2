{-# language
    CApiFFI
  , FlexibleInstances
  , ForeignFunctionInterface
  , MultiParamTypeClasses
  , TupleSections
  , TypeFamilies
  #-}

module Data.Number.Flint.Fmpz.LLL.FFI (
  -- * LLL reduction
    FmpzLLL (..)
  , CFmpzLLL (..)
  , newFmpzLLL
  , newFmpzLLLDefault
  , withFmpzLLL
  , withNewFmpzLLLDefault
  -- * Parameter manipulation
  , fmpz_lll_context_init_default
  , fmpz_lll_context_init
  -- ** Representation type
  , gram
  , z_basis
  -- ** Gram type
  , approx
  , exact
  -- * Random parameter generation
  , fmpz_lll_randtest
  -- * Heuristic dot product
  , fmpz_lll_heuristic_dot
  -- * The various Babai\'s
  , fmpz_lll_check_babai
  , fmpz_lll_check_babai_heuristic_d
  , fmpz_lll_check_babai_heuristic
  , fmpz_lll_advance_check_babai
  , fmpz_lll_advance_check_babai_heuristic_d
  -- * Shift
  , fmpz_lll_shift
  -- * Varieties of LLL
  , fmpz_lll_d
  , fmpz_lll_d_heuristic
  , fmpz_lll_mpf2
  , fmpz_lll_mpf
  , fmpz_lll_wrapper
  , fmpz_lll_d_with_removal
  , fmpz_lll_d_heuristic_with_removal
  , fmpz_lll_mpf2_with_removal
  , fmpz_lll_mpf_with_removal
  , fmpz_lll_wrapper_with_removal
  , fmpz_lll_d_with_removal_knapsack
  , fmpz_lll_wrapper_with_removal_knapsack
  -- * ULLL
  , fmpz_lll_with_removal_ulll
  -- * LLL-reducedness
  , fmpz_lll_is_reduced_d
  , fmpz_lll_is_reduced
  -- * Modified ULLL
  , fmpz_lll_storjohann_ulll
  -- * Main LLL functions
  , fmpz_lll
  , fmpz_lll_with_removal
) where 

-- LLL reduction ---------------------------------------------------------------

import Foreign.C.String
import Foreign.C.Types
import Foreign.ForeignPtr
import Foreign.Ptr ( Ptr, FunPtr, plusPtr )
import Foreign.Storable
import Foreign.Marshal ( free )

import Data.Number.Flint.Flint
import Data.Number.Flint.Fmpz
import Data.Number.Flint.Fmpz.Mat
import Data.Number.Flint.Support.D.Mat
import Data.Number.Flint.Support.Mpf.Mat

#include <flint/flint.h>

#include <flint/fmpz.h>
#include <flint/fmpz_lll.h>

-- representation type ---------------------------------------------------------

newtype Rep = Rep { _Rep :: CInt }

#{enum Rep, Rep
  , gram    = GRAM
  , z_basis = Z_BASIS
  }

newtype Gram = Gram { _Gram :: CInt }

#{enum Gram, Gram
  , approx = APPROX
  , exact  = EXACT
  }
 
-- fmpz__lll_t -----------------------------------------------------------------

data FmpzLLL = FmpzLLL {-# UNPACK #-} !(ForeignPtr CFmpzLLL)
data CFmpzLLL = CFmpzLLL {
  delta :: CDouble,
  eta   :: CDouble,
  rt    :: Rep,
  gt    :: Gram
  }

instance Storable CFmpzLLL where
  {-# INLINE sizeOf #-}
  sizeOf _ = #{size fmpz_lll_t}
  {-# INLINE alignment #-}
  alignment _ = #{alignment fmpz_lll_t}
  peek = error "CFmpzLLL.peek: Not defined"
  poke = error "CFmpzLLL.poke: Not defined"

newFmpzLLL delta eta rt gt = do
  p <- mallocForeignPtr
  withForeignPtr p $ \p -> fmpz_lll_context_init p delta eta rt gt
  -- addForeignPtrFinalizer free p
  return $ FmpzLLL p

newFmpzLLLDefault = do
  p <- mallocForeignPtr
  withForeignPtr p fmpz_lll_context_init_default
  -- addForeignPtrFinalizer free p
  return $ FmpzLLL p

{-# INLINE withFmpzLLL #-}
withFmpzLLL (FmpzLLL p) f = do
  withForeignPtr p $ \fp -> f fp >>= return . (FmpzLLL p,)

withNewFmpzLLLDefault f = do
  x <- newFmpzLLLDefault
  withFmpzLLL x $ \x -> f x

-- fmpz_gram_t -----------------------------------------------------------------

data FmpzGram = FmpzGram {-# UNPACK #-} !(ForeignPtr CFmpzGram)
data CFmpzGram = CFlintLib CFmpzGram

-- Parameter manipulation ------------------------------------------------------

-- These functions are used to initialise LLL context objects which are of
-- the type @fmpz_lll_t@. These objects contain all information about the
-- options governing the reduction using this module\'s functions including
-- the LLL parameters delta and eta, the representation type of the input
-- matrix (whether it is a lattice basis or a Gram matrix), and the type of
-- Gram matrix to be used during L^2 (approximate or exact).
--
-- | /fmpz_lll_context_init_default/ /fl/ 
-- 
-- Sets @fl->delta@, @fl->eta@, @fl->rt@ and @fl->gt@ to their default
-- values, 0.99, 0.51, \(Z\_BASIS\) and \(APPROX\) respectively.
foreign import ccall "fmpz_lll.h fmpz_lll_context_init_default"
  fmpz_lll_context_init_default :: Ptr CFmpzLLL -> IO ()

-- | /fmpz_lll_context_init/ /fl/ /delta/ /eta/ /rt/ /gt/ 
-- 
-- Sets @fl->delta@, @fl->eta@, @fl->rt@ and @fl->gt@ to @delta@, @eta@,
-- @rt@ and @gt@ (given as input) respectively. @delta@ and @eta@ are the
-- L^2 parameters. @delta@ and @eta@ must lie in the intervals
-- \((0.25, 1)\) and (0.5, sqrt{@delta@}) respectively. The representation
-- type is input using @rt@ and can have the values \(Z\_BASIS\) for a
-- lattice basis and \(GRAM\) for a Gram matrix. The Gram type to be used
-- during computation can be specified using @gt@ which can assume the
-- values \(APPROX\) and \(EXACT\). Note that @gt@ has meaning only when
-- @rt@ is \(Z\_BASIS\).
foreign import ccall "fmpz_lll.h fmpz_lll_context_init"
  fmpz_lll_context_init :: Ptr CFmpzLLL -> CDouble -> CDouble -> Rep -> Gram -> IO ()

-- Random parameter generation -------------------------------------------------

-- | /fmpz_lll_randtest/ /fl/ /state/ 
-- 
-- Sets @fl->delta@ and @fl->eta@ to random values in the interval
-- \((0.25, 1)\) and (0.5, sqrt{@delta@}) respectively. @fl->rt@ is set to
-- \(GRAM\) or \(Z\_BASIS\) and @fl->gt@ is set to \(APPROX\) or \(EXACT\)
-- in a pseudo random way.
foreign import ccall "fmpz_lll.h fmpz_lll_randtest"
  fmpz_lll_randtest :: Ptr CFmpzLLL -> Ptr CFRandState -> IO ()

-- Heuristic dot product -------------------------------------------------------

-- | /fmpz_lll_heuristic_dot/ /vec1/ /vec2/ /len2/ /B/ /k/ /j/ /exp_adj/ 
-- 
-- Computes the dot product of two vectors of doubles @vec1@ and @vec2@,
-- which are respectively @double@ approximations (up to scaling by a power
-- of 2) to rows @k@ and @j@ in the exact integer matrix @B@. If massive
-- cancellation is detected an exact computation is made.
-- 
-- The exact computation is scaled by @2^{-exp_adj@}, where
-- @exp_adj = r2 + r1@ where \(r2\) is the exponent for row @j@ and \(r1\)
-- is the exponent for row @k@ (i.e. row @j@ is notionally thought of as
-- being multiplied by \(2^{r2}\), etc.).
-- 
-- The final dot product computed by this function is then notionally the
-- return value times @2^{exp_adj@}.
foreign import ccall "fmpz_lll.h fmpz_lll_heuristic_dot"
  fmpz_lll_heuristic_dot :: Ptr CDouble -> Ptr CDouble -> CLong -> Ptr CFmpzMat -> CLong -> CLong -> CLong -> IO CDouble

-- The various Babai\'s --------------------------------------------------------

-- | /fmpz_lll_check_babai/ /kappa/ /B/ /U/ /mu/ /r/ /s/ /appB/ /expo/ /A/ /a/ /zeros/ /kappamax/ /n/ /fl/ 
-- 
-- Performs floating point size reductions of the @kappa@-th row of @B@ by
-- all of the previous rows, uses d_mats @mu@ and @r@ for storing the GSO
-- data. @U@ is used to capture the unimodular transformations if it is not
-- \(NULL\). The @double@ array @s@ will contain the size of the @kappa@-th
-- row if it were moved into position \(i\). The d_mat @appB@ is an
-- approximation of @B@ with each row receiving an exponent stored in
-- @expo@ which gets populated only when needed. The d_mat @A->appSP@ is an
-- approximation of the Gram matrix whose entries are scalar products of
-- the rows of @B@ and is used when @fl->gt@ == \(APPROX\). When @fl->gt@
-- == \(EXACT\) the fmpz_mat @A->exactSP@ (the exact Gram matrix) is used.
-- The index @a@ is the smallest row index which will be reduced from the
-- @kappa@-th row. Index @zeros@ is the number of zero rows in the matrix.
-- @kappamax@ is the highest index which has been size-reduced so far, and
-- @n@ is the number of columns you want to consider. @fl@ is an LLL (L^2)
-- context object. The output is the value -1 if the process fails (usually
-- due to insufficient precision) or 0 if everything was successful. These
-- descriptions will be true for the future Babai procedures as well.
foreign import ccall "fmpz_lll.h fmpz_lll_check_babai"
  fmpz_lll_check_babai :: CInt -> Ptr CFmpzMat -> Ptr CFmpzMat -> Ptr CDMat -> Ptr CDMat -> Ptr CDouble -> Ptr CDMat -> Ptr CInt -> Ptr CFmpzGram -> CInt -> CInt -> CInt -> CInt -> Ptr CFmpzLLL -> IO CInt

-- | /fmpz_lll_check_babai_heuristic_d/ /kappa/ /B/ /U/ /mu/ /r/ /s/ /appB/ /expo/ /A/ /a/ /zeros/ /kappamax/ /n/ /fl/ 
-- 
-- Same as @fmpz_lll_check_babai@ but using the heuristic inner product
-- rather than a purely floating point inner product. The heuristic will
-- compute at full precision when there is cancellation.
foreign import ccall "fmpz_lll.h fmpz_lll_check_babai_heuristic_d"
  fmpz_lll_check_babai_heuristic_d :: CInt -> Ptr CFmpzMat -> Ptr CFmpzMat -> Ptr CDMat -> Ptr CDMat -> Ptr CDouble -> Ptr CDMat -> Ptr CInt -> Ptr CFmpzGram -> CInt -> CInt -> CInt -> CInt -> Ptr CFmpzLLL -> IO CInt

-- | /fmpz_lll_check_babai_heuristic/ /kappa/ /B/ /U/ /mu/ /r/ /s/ /appB/ /A/ /a/ /zeros/ /kappamax/ /n/ /tmp/ /rtmp/ /prec/ /fl/ 
-- 
-- This function is like the @mpf@ version of
-- @fmpz_lll_check_babai_heuristic_d@. However, it also inherits some
-- temporary @mpf_t@ variables @tmp@ and @rtmp@.
foreign import ccall "fmpz_lll.h fmpz_lll_check_babai_heuristic"
  fmpz_lll_check_babai_heuristic :: CInt -> Ptr CFmpzMat -> Ptr CFmpzMat -> Ptr CMpfMat -> Ptr CMpfMat -> Ptr CMpf -> Ptr CMpfMat -> Ptr CFmpzGram -> CInt -> CInt -> CInt -> CInt -> Ptr CMpf -> Ptr CMpf -> CFBitCnt -> Ptr CFmpzLLL -> IO CInt

-- | /fmpz_lll_advance_check_babai/ /cur_kappa/ /kappa/ /B/ /U/ /mu/ /r/ /s/ /appB/ /expo/ /A/ /a/ /zeros/ /kappamax/ /n/ /fl/ 
-- 
-- This is a Babai procedure which is used when size reducing a vector
-- beyond an index which LLL has reached. @cur_kappa@ is the index behind
-- which we can assume @B@ is LLL reduced, while @kappa@ is the vector to
-- be reduced. This procedure only size reduces the @kappa@-th row by
-- vectors upto @cur_kappa@, textbf{not} @kappa - 1@.
foreign import ccall "fmpz_lll.h fmpz_lll_advance_check_babai"
  fmpz_lll_advance_check_babai :: CInt -> CInt -> Ptr CFmpzMat -> Ptr CFmpzMat -> Ptr CDMat -> Ptr CDMat -> Ptr CDouble -> Ptr CDMat -> Ptr CInt -> Ptr CFmpzGram -> CInt -> CInt -> CInt -> CInt -> Ptr CFmpzLLL -> IO CInt

-- | /fmpz_lll_advance_check_babai_heuristic_d/ /cur_kappa/ /kappa/ /B/ /U/ /mu/ /r/ /s/ /appB/ /expo/ /A/ /a/ /zeros/ /kappamax/ /n/ /fl/ 
-- 
-- Same as @fmpz_lll_advance_check_babai@ but using the heuristic inner
-- product rather than a purely floating point inner product. The heuristic
-- will compute at full precision when there is cancellation.
foreign import ccall "fmpz_lll.h fmpz_lll_advance_check_babai_heuristic_d"
  fmpz_lll_advance_check_babai_heuristic_d :: CInt -> CInt -> Ptr CFmpzMat -> Ptr CFmpzMat -> Ptr CDMat -> Ptr CDMat -> Ptr CDouble -> Ptr CDMat -> Ptr CInt -> Ptr CFmpzGram -> CInt -> CInt -> CInt -> CInt -> Ptr CFmpzLLL -> IO CInt

-- Shift -----------------------------------------------------------------------

-- | /fmpz_lll_shift/ /B/ 
-- 
-- Computes the largest number of non-zero entries after the diagonal in
-- @B@.
foreign import ccall "fmpz_lll.h fmpz_lll_shift"
  fmpz_lll_shift :: Ptr CFmpzMat -> IO CInt

-- Varieties of LLL ------------------------------------------------------------

-- These programs implement ideas from the book chapter < [Stehle2010]>.
-- The list of function here that are heuristic in nature and may return
-- with \(B\) unreduced - that is to say, not do their job - includes (but
-- is not necessarily limited to): * @fmpz_lll_d@ * @fmpz_lll_d_heuristic@
-- * @fmpz_lll_d_heuristic_with_removal@ * @fmpz_lll_d_with_removal@ *
-- @fmpz_lll_d_with_removal_knapsack@
--
-- | /fmpz_lll_d/ /B/ /U/ /fl/ 
-- 
-- This is a mildly greedy version of floating point LLL using doubles
-- only. It tries the fast version of the Babai algorithm
-- (@fmpz_lll_check_babai@). If that fails, then it switches to the
-- heuristic version (@fmpz_lll_check_babai_heuristic_d@) for only one loop
-- and switches right back to the fast version. It reduces @B@ in place.
-- @U@ is the matrix used to capture the unimodular transformations if it
-- is not \(NULL\). An exception is raised if \(U != NULL\) and
-- \(U->r != d\), where \(d\) is the lattice dimension. @fl@ is the context
-- object containing information containing the LLL parameters delta and
-- eta. The function can perform reduction on both the lattice basis as
-- well as its Gram matrix. The type of lattice representation can be
-- specified via the parameter @fl->rt@. The type of Gram matrix to be used
-- in computation (approximate or exact) can also be specified through the
-- variable @fl->gt@ (applies only if @fl->rt@ == \(Z\_BASIS\)).
foreign import ccall "fmpz_lll.h fmpz_lll_d"
  fmpz_lll_d :: Ptr CFmpzMat -> Ptr CFmpzMat -> Ptr CFmpzLLL -> IO CInt

-- | /fmpz_lll_d_heuristic/ /B/ /U/ /fl/ 
-- 
-- This LLL reduces @B@ in place using doubles only. It is similar to
-- @fmpz_lll_d@ but only uses the heuristic inner products which attempt to
-- detect cancellations.
foreign import ccall "fmpz_lll.h fmpz_lll_d_heuristic"
  fmpz_lll_d_heuristic :: Ptr CFmpzMat -> Ptr CFmpzMat -> Ptr CFmpzLLL -> IO CInt

-- | /fmpz_lll_mpf2/ /B/ /U/ /prec/ /fl/ 
-- 
-- This is LLL using @mpf@ with the given precision, @prec@ for the
-- underlying GSO. It reduces @B@ in place like the other LLL functions.
-- The \(mpf2\) in the function name refers to the way the @mpf_t@\'s are
-- initialised.
foreign import ccall "fmpz_lll.h fmpz_lll_mpf2"
  fmpz_lll_mpf2 :: Ptr CFmpzMat -> Ptr CFmpzMat -> CFBitCnt -> Ptr CFmpzLLL -> IO CInt

-- | /fmpz_lll_mpf/ /B/ /U/ /fl/ 
-- 
-- A wrapper of @fmpz_lll_mpf2@. This currently begins with
-- \(prec == D_BITS\), then for the first 20 loops, increases the precision
-- one limb at a time. After 20 loops, it doubles the precision each time.
-- There is a proof that this will eventually work. The return value of
-- this function is 0 if the LLL is successful or -1 if the precision maxes
-- out before @B@ is LLL-reduced.
foreign import ccall "fmpz_lll.h fmpz_lll_mpf"
  fmpz_lll_mpf :: Ptr CFmpzMat -> Ptr CFmpzMat -> Ptr CFmpzLLL -> IO CInt

-- | /fmpz_lll_wrapper/ /B/ /U/ /fl/ 
-- 
-- A wrapper of the above procedures. It begins with the greediest version
-- (@fmpz_lll_d@), then adapts to the version using heuristic inner
-- products only (@fmpz_lll_d_heuristic@) if \(fl->rt == Z\_BASIS\) and
-- \(fl->gt == APPROX\), and finally to the mpf version (@fmpz_lll_mpf@) if
-- needed.
-- 
-- @U@ is the matrix used to capture the unimodular transformations if it
-- is not \(NULL\). An exception is raised if \(U != NULL\) and
-- \(U->r != d\), where \(d\) is the lattice dimension. @fl@ is the context
-- object containing information containing the LLL parameters delta and
-- eta. The function can perform reduction on both the lattice basis as
-- well as its Gram matrix. The type of lattice representation can be
-- specified via the parameter @fl->rt@. The type of Gram matrix to be used
-- in computation (approximate or exact) can also be specified through the
-- variable @fl->gt@ (applies only if @fl->rt@ == \(Z\_BASIS\)).
foreign import ccall "fmpz_lll.h fmpz_lll_wrapper"
  fmpz_lll_wrapper :: Ptr CFmpzMat -> Ptr CFmpzMat -> Ptr CFmpzLLL -> IO CInt

-- | /fmpz_lll_d_with_removal/ /B/ /U/ /gs_B/ /fl/ 
-- 
-- Same as @fmpz_lll_d@ but with a removal bound, @gs_B@. The return value
-- is the new dimension of @B@ if removals are desired.
foreign import ccall "fmpz_lll.h fmpz_lll_d_with_removal"
  fmpz_lll_d_with_removal :: Ptr CFmpzMat -> Ptr CFmpzMat -> Ptr CFmpz -> Ptr CFmpzLLL -> IO CInt

-- | /fmpz_lll_d_heuristic_with_removal/ /B/ /U/ /gs_B/ /fl/ 
-- 
-- Same as @fmpz_lll_d_heuristic@ but with a removal bound, @gs_B@. The
-- return value is the new dimension of @B@ if removals are desired.
foreign import ccall "fmpz_lll.h fmpz_lll_d_heuristic_with_removal"
  fmpz_lll_d_heuristic_with_removal :: Ptr CFmpzMat -> Ptr CFmpzMat -> Ptr CFmpz -> Ptr CFmpzLLL -> IO CInt

-- | /fmpz_lll_mpf2_with_removal/ /B/ /U/ /prec/ /gs_B/ /fl/ 
-- 
-- Same as @fmpz_lll_mpf2@ but with a removal bound, @gs_B@. The return
-- value is the new dimension of @B@ if removals are desired.
foreign import ccall "fmpz_lll.h fmpz_lll_mpf2_with_removal"
  fmpz_lll_mpf2_with_removal :: Ptr CFmpzMat -> Ptr CFmpzMat -> CFBitCnt -> Ptr CFmpz -> Ptr CFmpzLLL -> IO CInt

-- | /fmpz_lll_mpf_with_removal/ /B/ /U/ /gs_B/ /fl/ 
-- 
-- A wrapper of @fmpz_lll_mpf2_with_removal@. This currently begins with
-- \(prec == D\_BITS\), then for the first 20 loops, increases the
-- precision one limb at a time. After 20 loops, it doubles the precision
-- each time. There is a proof that this will eventually work. The return
-- value of this function is the new dimension of @B@ if removals are
-- desired or -1 if the precision maxes out before @B@ is LLL-reduced.
foreign import ccall "fmpz_lll.h fmpz_lll_mpf_with_removal"
  fmpz_lll_mpf_with_removal :: Ptr CFmpzMat -> Ptr CFmpzMat -> Ptr CFmpz -> Ptr CFmpzLLL -> IO CInt

-- | /fmpz_lll_wrapper_with_removal/ /B/ /U/ /gs_B/ /fl/ 
-- 
-- A wrapper of the procedures implementing the base case LLL with the
-- addition of the removal boundary. It begins with the greediest version
-- (@fmpz_lll_d_with_removal@), then adapts to the version using heuristic
-- inner products only (@fmpz_lll_d_heuristic_with_removal@) if
-- \(fl->rt == Z\_BASIS\) and \(fl->gt == APPROX\), and finally to the mpf
-- version (@fmpz_lll_mpf_with_removal@) if needed.
foreign import ccall "fmpz_lll.h fmpz_lll_wrapper_with_removal"
  fmpz_lll_wrapper_with_removal :: Ptr CFmpzMat -> Ptr CFmpzMat -> Ptr CFmpz -> Ptr CFmpzLLL -> IO CInt

-- | /fmpz_lll_d_with_removal_knapsack/ /B/ /U/ /gs_B/ /fl/ 
-- 
-- This is floating point LLL specialized to knapsack-type lattices. It
-- performs early size reductions occasionally which makes things faster in
-- the knapsack case. Otherwise, it is similar to
-- @fmpz_lll_d_with_removal@.
foreign import ccall "fmpz_lll.h fmpz_lll_d_with_removal_knapsack"
  fmpz_lll_d_with_removal_knapsack :: Ptr CFmpzMat -> Ptr CFmpzMat -> Ptr CFmpz -> Ptr CFmpzLLL -> IO CInt

-- | /fmpz_lll_wrapper_with_removal_knapsack/ /B/ /U/ /gs_B/ /fl/ 
-- 
-- A wrapper of the procedures implementing the LLL specialized to
-- knapsack-type lattices. It begins with the greediest version and the
-- engine of this version, (@fmpz_lll_d_with_removal_knapsack@), then
-- adapts to the version using heuristic inner products only
-- (@fmpz_lll_d_heuristic_with_removal@) if \(fl->rt == Z\_BASIS\) and
-- \(fl->gt == APPROX\), and finally to the mpf version
-- (@fmpz_lll_mpf_with_removal@) if needed.
foreign import ccall "fmpz_lll.h fmpz_lll_wrapper_with_removal_knapsack"
  fmpz_lll_wrapper_with_removal_knapsack :: Ptr CFmpzMat -> Ptr CFmpzMat -> Ptr CFmpz -> Ptr CFmpzLLL -> IO CInt

-- ULLL ------------------------------------------------------------------------

-- | /fmpz_lll_with_removal_ulll/ /FM/ /UM/ /new_size/ /gs_B/ /fl/ 
-- 
-- ULLL is a new style of LLL which does adjoins an identity matrix to the
-- input lattice @FM@, then scales the lattice down to @new_size@ bits and
-- reduces this augmented lattice. This tends to be more stable numerically
-- than traditional LLL which means higher dimensions can be attacked using
-- doubles. In each iteration a new identity matrix is adjoined to the
-- truncated lattice. @UM@ is used to capture the unimodular
-- transformations, while @gs_B@ and @fl@ have the same role as in the
-- previous routines. The function is optimised for factoring polynomials.
foreign import ccall "fmpz_lll.h fmpz_lll_with_removal_ulll"
  fmpz_lll_with_removal_ulll :: Ptr CFmpzMat -> Ptr CFmpzMat -> CLong -> Ptr CFmpz -> Ptr CFmpzLLL -> IO CInt

-- LLL-reducedness -------------------------------------------------------------

-- These programs implement ideas from the paper < [Villard2007]>. See
-- <https://arxiv.org/abs/cs/0701183> for the algorithm of Villard.
--
-- | /fmpz_lll_is_reduced_d/ /B/ /fl/ 
-- 
-- A non-zero return indicates the matrix is definitely reduced, that is,
-- that * @fmpz_mat_is_reduced@ or @fmpz_mat_is_reduced_gram@ (for the
-- first two) * @fmpz_mat_is_reduced_with_removal@ or
-- @fmpz_mat_is_reduced_gram_with_removal@ (for the last two) return
-- non-zero. A zero return value is inconclusive. The \(_d\) variants are
-- performed in machine precision, while the \(_mpfr\) uses a precision of
-- \(prec\) bits.
foreign import ccall "fmpz_lll.h fmpz_lll_is_reduced_d"
  fmpz_lll_is_reduced_d :: Ptr CFmpzMat -> Ptr CFmpzLLL -> IO CInt

-- | /fmpz_lll_is_reduced/ /B/ /fl/ /prec/ 
-- 
-- The return from these functions is always conclusive: the functions *
-- @fmpz_mat_is_reduced@ or @fmpz_mat_is_reduced_gram@ *
-- @fmpz_mat_is_reduced_with_removal@ or
-- @fmpz_mat_is_reduced_gram_with_removal@ are optimzied by calling the
-- above heuristics first and returning right away if they give a
-- conclusive answer.
foreign import ccall "fmpz_lll.h fmpz_lll_is_reduced"
  fmpz_lll_is_reduced :: Ptr CFmpzMat -> Ptr CFmpzLLL -> CFBitCnt -> IO CInt

-- Modified ULLL ---------------------------------------------------------------

-- | /fmpz_lll_storjohann_ulll/ /FM/ /new_size/ /fl/ 
-- 
-- Performs ULLL using @fmpz_mat_lll_storjohann@ as the LLL function.
foreign import ccall "fmpz_lll.h fmpz_lll_storjohann_ulll"
  fmpz_lll_storjohann_ulll :: Ptr CFmpzMat -> CLong -> Ptr CFmpzLLL -> IO ()

-- Main LLL functions ----------------------------------------------------------

-- | /fmpz_lll/ /B/ /U/ /fl/ 
-- 
-- Reduces @B@ in place according to the parameters specified by the LLL
-- context object @fl@.
-- 
-- This is the main LLL function which should be called by the user. It
-- currently calls the ULLL algorithm (without removals). The ULLL function
-- in turn calls a LLL wrapper which tries to choose an optimal LLL
-- algorithm, starting with a version using just doubles (ULLL tries to
-- maximise usage of this), then a heuristic LLL a full precision floating
-- point LLL if required.
-- 
-- @U@ is the matrix used to capture the unimodular transformations if it
-- is not \(NULL\). An exception is raised if \(U != NULL\) and
-- \(U->r != d\), where \(d\) is the lattice dimension. @fl@ is the context
-- object containing information containing the LLL parameters delta and
-- eta. The function can perform reduction on both the lattice basis as
-- well as its Gram matrix. The type of lattice representation can be
-- specified via the parameter @fl->rt@. The type of Gram matrix to be used
-- in computation (approximate or exact) can also be specified through the
-- variable @fl->gt@ (applies only if @fl->rt@ == \(Z\_BASIS\)).
foreign import ccall "fmpz_lll.h fmpz_lll"
  fmpz_lll :: Ptr CFmpzMat -> Ptr CFmpzMat -> Ptr CFmpzLLL -> IO ()

-- | /fmpz_lll_with_removal/ /B/ /U/ /gs_B/ /fl/ 
-- 
-- Reduces @B@ in place according to the parameters specified by the LLL
-- context object @fl@ and removes vectors whose squared Gram-Schmidt
-- length is greater than the bound @gs_B@. The return value is the new
-- dimension of @B@ to be considered for further computation.
-- 
-- This is the main LLL with removals function which should be called by
-- the user. Like @fmpz_lll@ it calls ULLL, but it also sets the
-- Gram-Schmidt bound to that supplied and does removals.
foreign import ccall "fmpz_lll.h fmpz_lll_with_removal"
  fmpz_lll_with_removal :: Ptr CFmpzMat -> Ptr CFmpzMat -> Ptr CFmpz -> Ptr CFmpzLLL -> IO CInt

