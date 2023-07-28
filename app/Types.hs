module Types where

import Data.Typeable
import Data.Number.Flint

printAllTypes = do
  print $ typeOf CAPRCLConfig
  print $ typeOf CAcb
  -- print $ typeOf CAcbCalcFunc
  -- print $ typeOf CAcbCalcIntegrateOpt
  -- print $ typeOf CAcbDftCrt
  -- print $ typeOf CAcbDftPre
  print $ typeOf CAcbMat
  -- print $ typeOf CAcbPoly
  print $ typeOf CAcf
  print $ typeOf CArb
  -- print $ typeOf CArbCalcFunc
  print $ typeOf CArbMat
  -- print $ typeOf CArbPoly
  -- print $ typeOf CArf
  print $ typeOf CArfInterval
  -- print $ typeOf CBernoulliRev
  print $ typeOf CBoolMat
  -- print $ typeOf CDLogPrecomp
  print $ typeOf CDMat
  print $ typeOf CDi
  print $ typeOf CDirichletChar
  -- print $ typeOf CDirichletGroup
  -- print $ typeOf CEcm
  -- print $ typeOf CF
  -- print $ typeOf CFBitCnt
  -- print $ typeOf CFRandState
  print $ typeOf CFlint
  print $ typeOf CFmpq
  print $ typeOf CFmpqMPoly
  -- print $ typeOf CFmpqMPolyCtx
  print $ typeOf CFmpqMPolyFactor
  print $ typeOf CFmpqMat
  print $ typeOf CFmpqPoly
  -- print $ typeOf CFmpz
  -- print $ typeOf CFmpzComb
  -- print $ typeOf CFmpzCombTemp
  print $ typeOf CFmpzFactor
  print $ typeOf CFmpzLLL
  print $ typeOf CFmpzMPoly
  -- print $ typeOf CFmpzMPolyCtx
  print $ typeOf CFmpzMPolyFactor
  print $ typeOf CFmpzMPolyQ
  print $ typeOf CFmpzMat
  -- print $ typeOf CFmpzModCtx
  print $ typeOf CFmpzModMPoly
  -- print $ typeOf CFmpzModMPolyCtx
  print $ typeOf CFmpzModMPolyFactor
  -- print $ typeOf CFmpzModMat
  print $ typeOf CFmpzModPoly
  print $ typeOf CFmpzModPolyFactor
  -- print $ typeOf CFmpzMultiCRT
  print $ typeOf CFmpzPoly
  print $ typeOf CFmpzPolyFactor
  print $ typeOf CFmpzPolyMat
  print $ typeOf CFmpzPolyQ
  -- print $ typeOf CFmpzPreInvN
  print $ typeOf CFmpzi
  -- print $ typeOf CFq
  -- print $ typeOf CFqCtx
  -- print $ typeOf CFqMat
  -- print $ typeOf CFqNMod
  print $ typeOf CFqNModCtx
  -- print $ typeOf CFqNModMPoly
  -- print $ typeOf CFqNModMPolyCtx
  print $ typeOf CFqNModMPolyFactor
  -- print $ typeOf CFqNModMat
  -- print $ typeOf CFqNModPoly
  print $ typeOf CFqNModPolyFactor
  print $ typeOf CFqPoly
  print $ typeOf CFqPolyFactor
  -- print $ typeOf CFqZech
  -- print $ typeOf CFqZechCtx
  -- print $ typeOf CFqZechMat
  -- print $ typeOf CFqZechPoly
  print $ typeOf CFqZechPolyFactor
  -- print $ typeOf CGmpRandstate
  -- print $ typeOf CMPolyCtx
  print $ typeOf CMag
  print $ typeOf CMp
  -- print $ typeOf CMpBitCnt
  -- print $ typeOf CMpLimb
  -- print $ typeOf CMpSLimb
  -- print $ typeOf CMpSize
  print $ typeOf CMpf
  -- print $ typeOf CMpfMat
  print $ typeOf CMpfr
  -- print $ typeOf CMpfrMat
  print $ typeOf CMpfrPrec
  print $ typeOf CMpfrRnd
  print $ typeOf CMpq
  print $ typeOf CMpz
  print $ typeOf CNF
  -- print $ typeOf CNFElem
  print $ typeOf CNFactor
  print $ typeOf CNMod
  -- print $ typeOf CNModDiscreteLogPohligHellman
  print $ typeOf CNModMPoly
  -- print $ typeOf CNModMPolyCtx
  print $ typeOf CNModMPolyFactor
  print $ typeOf CNModMat
  -- print $ typeOf CNModPoly
  print $ typeOf CNModPolyFactor
  print $ typeOf CNModPolyMat
  -- print $ typeOf CNPrimes
  print $ typeOf COrdering
  print $ typeOf CPSL2Z
  print $ typeOf CPadic
  print $ typeOf CPadicCtx
  print $ typeOf CPadicMat
  print $ typeOf CPadicPoly
  -- print $ typeOf CQQbar
  -- print $ typeOf CQadic
  print $ typeOf CQadicCtx
  print $ typeOf CQfb
  -- print $ typeOf CQs
  print $ typeOf CUnityZp
  -- print $ typeOf CUnityZpq
