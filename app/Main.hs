{-# language DataKinds, RankNTypes #-}

module Main where

import Test.QuickCheck

import System.IO.Unsafe

import Data.Typeable

import Foreign.Ptr
import Foreign.Marshal
import Foreign.Marshal.Array
import Foreign.Storable
import Foreign.C.String
import Foreign.C.Types
import Foreign.Marshal.Utils (new, with)

import GHC.TypeLits
import GHC.Exts

import Data.Proxy

import Control.Monad
import Control.Monad.Reader
import Text.Printf
import Data.List (permutations)

import qualified Data.Vector as Vector
import Data.Vector (Vector, (!))
import qualified Data.Vector.Algorithms.Merge as Vector (sort)
import Data.Group

import Data.Number.Flint

import Polynomial
import Types
import Modular

main = testMember
  
type RR = RF 128
type CC = CF 128

testCF = do
  let r = 2 :: RR
      theta = 2*pi/3 :: RR
      z = cis theta
      i = cis (pi/2) :: CC
  print z
  print $ z^3
  print $ polar z
  print $ realPart z
  print $ imagPart z
  print $ magnitude z
  
testContinuedFraction = do
  let n = 16
      x = sqrt (17 / 31) :: RF 128
      w = (fromRational (toRational x) :: Fmpq)^2
  printCF n w
  
printCF n w = do
  c <- _fmpz_vec_init n
  withFmpq w $ \w -> do
    withNewFmpq $ \rem -> do
      fmpq_get_cfrac c rem w n
  printCVec fmpz_print c n
    
testRF = do
  let dx = recip 1000 :: RF 1024
      x = map ((*dx) . fromInteger) [0..20000]
      y = map (besselJ 0) x
      [x', y'] = map (map toDouble) [x, y]
  writeFile "bessel.out" $ unlines
                         $ zipWith (printf "%18.12e %18.12e") x' y'

testNModPoly = do
  let n = 7
  poly <- newNModPoly n
  withNModPoly poly $ \poly -> do
    nmod_poly_set_coeff_ui poly 0 (fromIntegral $ pred n)
    nmod_poly_set_coeff_ui poly 1 1
  print poly
  let p12 = poly^12
  print p12
  print $ factor p12
            
testArbFmpzPoly = do
  let poly = fromList [3, 2, 1] :: FmpzPoly
      prec = 1024
  roots <- _acb_vec_init 2
  withFmpzPoly poly $ \poly -> do
    arb_fmpz_poly_complex_roots roots poly 0 prec
  forM_ [0..1] $ \j -> do
    acb_printn (roots `advancePtr` j) 16 arb_str_no_radius
    endl
  _acb_vec_clear roots 2
  
testFmpzPolyMat = do
  let poly = fromList [3, 2, 1] :: FmpzPoly
  a <- newFmpzPolyMat 3 5
  withFmpzPolyMat a $ \a -> do
    withCString "x" $ \x -> do 
      fmpz_poly_mat_print a x
    p <- fmpz_poly_mat_entry a 2 2
    withFmpzPoly poly $ \poly -> do
      fmpz_poly_set p poly
    withCString "x" $ \x -> do 
      fmpz_poly_mat_print a x

testFmpq = do
  let z, s :: Fmpq
      z = 2 // 7
      s = sum $ map (1//) [1..10]
  print z
  print $ z^2
  let b = bernoulliB 20
  print b
  print $ numerator b
  print $ denominator b
  print s
  
testRest = do
  x <- newFmpz
  withFmpz x $ \x -> do
    fmpz_set_ui x 7
    flag <- fmpz_print x
    endl
  let a = 15623679023253334147 :: Fmpz
      b = 13550662568090911171 :: Fmpz
      x = a * b
  print x
  print $ factor x
  withFmpz x $ \x ->
    withNewFmpzFactor $ \f -> do
      fmpz_factor f x
      fmpz_factor_print f
      endl
  r <- newFRandState
  replicateM_ 10 $ do
    withFRandState r $ \r -> do
      withFmpz x $ \x -> do
        fmpz_randbits x r 64
        putStr "random number: "
        fmpz_print x
        endl
        withNewFmpzFactor $ \f -> do
          fmpz_factor f x
          putStr "factorization: "
          fmpz_factor_print f
          endl
  l <- sample' arbitrary :: IO [Fmpz]
  print l
  let n = 10
  v <- _fmpz_vec_init n
  forM_ [0..fromIntegral n-1] $ \j -> do
    fmpz_set_si (v `advancePtr` j) (fromIntegral (j+1)^2)
  _fmpz_vec_print v n
  f <- newFmpzFactor
  forM_ [0..fromIntegral n-1] $ \j -> do
    withFmpzFactor f $ \f -> do
      fmpz_factor f (v `advancePtr` j)
      fmpz_factor_print f
      endl
  _fmpz_vec_clear v n
  forM_ [0..10] $ \j ->
    print $ hermitePolynomial j
  let poly = product $ map hermitePolynomial [0..10]
  mapM_ print $ factor poly
  a <- newFmpzMat 3 3
  withFmpzMat a fmpz_mat_one
  withFmpzMat a fmpz_mat_print_pretty; endl
  withFmpzMat a $ \a -> do
    p <- fmpz_mat_entry a 0 2
    fmpz_set_ui p 7
  withFmpzMat a fmpz_mat_print_pretty; endl
  d <- newDMat 3 3
  withDMat d $ \d ->
    withFmpzMat a $ \a ->
      fmpz_mat_get_d_mat d a
  withDMat d $ \d ->
    forM_ [0..2] $ \i -> do
      forM_ [0..2] $ \j -> do
        x <- d_mat_get_entry d i j
        print x
  poly <- newFmpqPoly
  withFmpqPoly poly $ \poly -> do
    fmpq_poly_legendre_p poly 7
  print poly
  withFmpqPoly poly $ \poly -> do
    withCString "x" $ \var -> do
      fmpq_poly_print_pretty_as_series poly var 
  print $ poly^3
  testFmpqMat
  testPadic
  testPadicMat
  testQadic
  testHilbert
  testPerm
  
endl = putStrLn ""

testNModMat = do
  state <- newFRandState  
  a <- newNModMat 3 5 7
  withNModMat a $ \a -> do
    withFRandState state $ \state -> do
      nmod_mat_randfull a state
    nmod_mat_print_pretty a

testArbMat = do
  let prec = 1024
      n = 5
  h <- newFmpqMat n n
  withFmpqMat h fmpq_mat_hilbert_matrix
  a <- newArbMatFromFmpqMat h prec
  withArbMat a $ \a -> arb_mat_inv a a prec
  print a
  withFmpqMat h $ \h -> fmpq_mat_inv h h
  print h

testQfb = do
  x <- newQfb 7 3 5
  print x
  withQfb x $ \x -> do
    qfb_inverse x x
    qfb_print x
    endl
    withNewFmpz $ \d -> do
      qfb_discriminant d x
      fmpz_print d
      endl
  return ()
  
testPadic = do
  withNewPadicCtx 7 0 128 padic_series $ \ctx -> do
    putStr "padic ctx: "
    padic_ctx_print ctx
    endl
    withNewPadic $ \x -> do
      padic_set_ui x 2 ctx
      padic_print x ctx
      endl
      padic_sqrt x x ctx
      padic_print x ctx
      endl
      CPadic a b c <- peek x
      putStrLn "examine padic structure:"
      fmpz_print a
      endl
      padic_neg x x ctx
      padic_print x ctx
      endl
      padic_mul x x x ctx
      padic_print x ctx
      endl
      v <- padic_get_val x
      print v
      prec <- padic_get_prec x
      print prec
      u <- padic_unit x
      fmpz_print u
      endl

testQadic = do
  let c = [1,10,9,8,8,0,2,9,1,3,1]
  withNewQadicCtx 11 4 0 128 "a" padic_series $ \ctx -> do
    CQadicCtx pctx _ _ _ _ <- peek ctx
    withNewQadic $ \x -> do
      withFmpzPoly (fromList [3,0,4,8]) $ \poly -> do
        padic_poly_set_fmpz_poly x poly pctx
      newton x c ctx
      putStr "x = "
      qadic_print_pretty x ctx
      putStr "\n"
      y <- horner x c ctx
      withQadic y $ \y -> do
        putStr "y = "
        qadic_print_pretty y ctx
        putStr "\n"
         
newton x c ctx = do
  withNewQadic $ \y ->
    withNewQadic $ \y' -> do
      qadic_set_ui y (head c) ctx
      qadic_set_ui y' 0 ctx
      withNewQadic $ \tmp -> 
        forM_ (tail c) $ \c -> do
          qadic_set_ui tmp c ctx
          qadic_mul y' y' x ctx
          qadic_add y' y' y ctx
          qadic_mul y y x ctx
          qadic_add y y tmp ctx
      is_zero <- qadic_is_zero y
      qadic_inv y' y' ctx
      qadic_mul y y y' ctx
      qadic_sub x x y ctx
      when (is_zero /= 1) $ newton x c ctx
  return ()

horner x c ctx = do
  y <- newQadic
  withQadic y $ \y -> do
    qadic_set_ui y (head c) ctx
    withNewQadic $ \tmp ->
      forM_ (tail c) $ \c -> do
        qadic_mul y y x ctx
        qadic_set_ui tmp c ctx
        qadic_add y y tmp ctx
  return y

testPadicMat = do
  let p = 11 :: Fmpz
  withNewPadicCtx p 0 128 padic_terse $ \ctx -> do
    mat <- newPadicMat 3 3 20
    withPadicMat mat $ \mat -> do
      withNewFmpqMat 3 3 $ \r -> do
        fmpq_mat_hilbert_matrix r
        padic_mat_set_fmpq_mat mat r ctx
      padic_mat_print mat ctx
      endl
      padic_mat_print_pretty mat ctx
      endl

testFmpqMat = do
  mat <- newFmpqMat 4 4
  poly <- newFmpqPoly
  withFmpqMat mat $ \mat -> do
    fmpq_mat_hilbert_matrix mat
    p <- fmpq_mat_entry mat 1 2
    print p
    fmpq_set_ui p 7 13
    fmpq_mat_print mat
    endl
    withNewFmpq $ \d -> do
      fmpq_mat_det d mat
      fmpq_print d
      endl
    withFmpqPoly poly $ \poly -> fmpq_mat_charpoly poly mat
  print poly
  
testHilbert = do
  putStrLn "testHilbert:"
  forM_ [1..10] $ \n -> do
    putStr $ show n ++ " "
    mat <- newFmpqMat n n
    withFmpqMat mat $ \mat -> do
      fmpq_mat_hilbert_matrix mat
      withNewFmpq $ \d -> do
        fmpq_mat_det d mat
        withNewFmpz $ \a -> do
          b <- newFmpz
          withFmpz b $ \b -> do
            fmpq_get_fmpz_frac a b d
          print $ factor b

testPerm = do
  let n = 12
  sigma@[a, b, c] <- replicateM 3 (_perm_init 12)
  zipWithM_ pokeArray sigma [
      [1,0,3,2,5,4,8,9,6,7,11,10]
    , [3,0,9,1,10,2,11,6,4,5,8,7]
    , [0,2,4,1,6,7,9,10,11,3,5,8]]
  forM_ sigma $ \p -> do
    _perm_print_pretty p n
    endl
  -- a * b * c
  d <- _perm_init n
  _perm_compose d b a n
  _perm_compose d c d n
  _perm_print_pretty d n
  endl
  -- a * b
  _perm_compose d b a n
  _perm_print_pretty d n; endl
  endl
  t <- newPSL2Z_ 1 1 0 1
  p <- _perm_init n
  withPSL2Z t $ \t -> do
    psl2z_get_perm p a c n t
  _perm_print_pretty p n
  endl
  _perm_print_pretty c n
  endl
  endl
  g <- newPSL2Z_ (-9444732965739290427388)
               148754559975189931622431
               4521254170618233912705
               (-71209760733946064941912)
  withPSL2Z g $ \g -> do
    psl2z_get_perm p a c n g
  _perm_print_pretty p n
  endl
  res <- _perm_init n
  withNewPSL2ZWord $ \w -> do
    withPSL2Z g $ \g -> do
      psl2z_get_word w g
      _perm_set_word res a c n w
  _perm_print_pretty res n
  endl
  return ()

testFq = do
  ctx <- newFqCtx 7 5 "a"
  x <- newFq ctx
  tmp <- newFq ctx
  withFqCtx ctx $ \ctx -> do
    fq_ctx_print ctx
    endl
    withFq x $ \x -> do
      withFq tmp $ \tmp -> do 
        withFmpzPoly (fromList [0, 3, 1]) $ \poly -> fq_set x poly ctx
        fq_print_pretty x ctx
        endl
        endl
        forM_ [0..4] $ \j -> do 
          fq_frobenius tmp x j ctx
          putStr $ show j ++ " "
          fq_print_pretty tmp ctx
          endl
        endl

testFqNModPoly = do
  state <- newFRandState
  ctx <- newFqNModCtx 7 4 "a"
  poly <- newFqNModPoly ctx
  pre <- newFqNMod ctx
  fac <- newFqNModPolyFactor ctx
  withFRandState state $ \state -> do
    replicateM_ 10 $ do
      withFqNModCtx ctx $ \ctx -> do
        fq_nmod_ctx_print ctx
        withFqNModPoly poly $ \poly -> do
          fq_nmod_poly_randtest poly state 5 ctx
          withCString "x" $ \var -> do
            fq_nmod_poly_print_pretty poly var ctx
            endl
            withFqNMod pre $ \pre -> do
              withFqNModPolyFactor fac $ \fac -> do
                fq_nmod_poly_factor fac pre poly ctx
                withCString "x" $ \var -> do
                  putStrLn "factorization:"
                  fq_nmod_poly_factor_print_pretty fac var ctx
          
testFmpqPoly = do
  poly <- newFmpqPoly
  withFmpqPoly poly $ \poly -> do
    arith_bernoulli_polynomial poly 12
  print poly

testFmpzMPoly = do
  let n = 4
  ctx <- newFmpzMPolyCtx n ord_lex
  poly <- newFmpzMPoly ctx
  withFmpzMPolyCtx ctx $ \ctx -> do
    withFmpzMPoly poly $ \poly -> do
      forM_ [0..fromIntegral n] $ \j -> do 
        fmpz_mpoly_symmetric poly j ctx
        fmpz_mpoly_print_pretty poly nullPtr ctx
        endl
  endl  
  x <- newArray =<< traverse newCString [[c] | c <- ['A'..'z']]
  withFmpzMPolyCtx ctx $ \ctx -> do
    withFmpzMPoly poly $ \poly -> do
      forM_ [0..fromIntegral n] $ \j -> do 
        fmpz_mpoly_symmetric poly j ctx
        fmpz_mpoly_print_pretty poly x ctx
        endl 
  endl


testFmpzMPolyQ = do
  ctx <- newFmpzMPolyCtx 7 ord_lex
  num <- newFmpzMPoly ctx
  den <- newFmpzMPoly ctx
  r <- newFmpzMPolyQ ctx
  print $ typeOf num
  print $ typeOf den
  withFmpzMPolyCtx ctx $ \ctx -> do
    withFmpzMPoly num $ \num -> do
      withFmpzMPoly den $ \den -> do
        fmpz_mpoly_symmetric num 1 ctx
        fmpz_mpoly_symmetric den 2 ctx
        print $ typeOf num
        print $ typeOf num
    withFmpzMPolyQ r $ \r -> do
      fmpz_mpoly_q_gen r 5 ctx
      fmpz_mpoly_q_inv r r ctx
      fmpz_mpoly_q_print_pretty r nullPtr ctx
      endl
  endl
  gens <- forM [0..6] $ \j -> mkGen j ctx
  tmp <- newFmpzMPolyQ ctx
  print $ typeOf tmp
  withFmpzMPolyCtx ctx $ \ctx -> do
    withFmpzMPolyQ tmp $ \tmp -> do
      withFmpzMPolyQ r $ \r -> do  
        forM_ gens $ \g -> do
          withFmpzMPolyQ g $ \g -> do
            fmpz_mpoly_q_set r g ctx
            fmpz_mpoly_q_inv r r ctx
            fmpz_mpoly_q_add r r g ctx
            fmpz_mpoly_q_add tmp tmp r ctx
            fmpz_mpoly_q_print_pretty r nullPtr ctx
            endl
        putStrLn $ "\nresult of type \"" ++ show (typeOf tmp) ++ "\":\n"
        fmpz_mpoly_q_print_pretty tmp nullPtr ctx
        endl
    putStrLn "\nnumerator:\n" 
    withFmpzMPolyQNumerator tmp $ \tmp -> do
      fmpz_mpoly_print_pretty tmp nullPtr ctx
      endl
    putStrLn "\ndenominator:\n"
    withFmpzMPolyQDenominator tmp $ \tmp -> do
      fmpz_mpoly_print_pretty tmp nullPtr ctx
      endl
  endl
        
mkGen j ctx = do
  r <- newFmpzMPolyQ ctx
  withFmpzMPolyCtx ctx $ \ctx -> do
    withFmpzMPolyQ r $ \r -> do
      fmpz_mpoly_q_gen r j ctx
  return r

testArb = do
  let prec = 1024
  withNewArb $ \x -> do
    withNewArb $ \pi -> do
      arb_const_pi pi prec
      arb_sqrt x pi prec
      arb_printn x prec arb_str_no_radius
      endl
      arb_mul x x x prec
      arb_printn x prec arb_str_no_radius
      endl
      arb_sub x pi x prec
      arb_printn x prec arb_str_no_radius
      endl
      arb_const_pi x prec
      arb_print x
      endl
      arb_printd x 16
      endl

testArbRead = do
  let prec = 1024
      decPrec = round $ fromIntegral prec * logBase 10 2
      bits = 128
  state <- newFRandState
  withFRandState state $ \state -> do
    withNewArb $ \x -> do
      replicateM_ 100 $ do
        arb_randtest x state prec bits
        -- arb_printn x 16 arb_str_no_radius
        -- endl
        cs <- arb_get_str x (fromIntegral decPrec) arb_str_no_radius
        s <- take decPrec <$> peekCString cs
        free cs
        let y = read s :: RF 1024
        when (isNaN y) $ do
          putStr "--> "
          arb_printn x 16 arb_str_no_radius
          endl

      
testAcb = do
  let prec = 1024
  withNewAcb $ \x -> do
    acb_set_si_si x 3 7
    acb_printn x 16 arb_str_no_radius
    endl
    acb_sqrt x x prec
    acb_printn x 16 arb_str_no_radius
    endl
    acb_mul x x x prec
    acb_printn x 16 arb_str_no_radius
    endl
    withNewArb $ \a -> do
      acb_abs a x prec
      arb_mul a a a prec
      arb_printn a 16 arb_str_no_radius
      endl
    withNewAcb $ \pi -> do
      withNewAcb $ \w -> do
        acb_const_pi pi prec
        forM_ [2..10] $ \n -> do
          acb_pow_si w pi n prec
          acb_set_si_si x n 0
          acb_zeta x x prec
          acb_div x x w prec
          acb_inv x x prec
          acb_printn x 32 arb_str_no_radius
          endl
        endl
        
testNF = do
  let poly = fromList [6,-24,42,-46,55,-86,101,-73,38,-20,9,-2,1] :: FmpqPoly
      z = fromList [0, 1] :: FmpqPoly
  nf <- newNF poly
  x <- newNFElem nf
  withNF nf $ \nf -> do 
    withNFElem x $ \x -> do
      withFmpqPoly z $ \z -> do
        nf_elem_set_fmpq_poly x z nf
      nf_elem_pow x x 12 nf
      withCString "a" $ \a -> do
        nf_elem_print_pretty x nf a
        endl
        r <- nfRep x nf
        withFmpqMat r $ \r -> do
          fmpq_mat_print r
  endl

testNF' = do
  let poly = fromList [1,10,32,38,58,25,25,-12,-6,-11,1,0,1] :: FmpqPoly
      z = fromList [0, 1] :: FmpqPoly
  nf <- newNF poly
  x <- newNFElem nf
  withNF nf $ \f -> do 
    withNFElem x $ \x -> do
      withFmpqPoly z $ \z -> do
        nf_elem_set_fmpq_poly x z f
      withNewNFElem nf $ \y -> do
        forM_ [0..11] $ \j -> do 
          nf_elem_pow y x j f
          withCString "a" $ \a -> do
            nf_elem_print_pretty y f a
            endl
          withNewFmpq $ \q -> do
            nf_elem_norm q y f
            fmpq_print q
            endl
           
nfRep x nf = do
  (_, n) <- withNewFmpqPoly $ \poly -> do
    nf_elem_get_fmpq_poly poly x nf
    fmpq_poly_degree poly
  a <- newFmpqMat (n+1) (n+1)
  withFmpqMat a $ \a -> do
    nf_elem_rep_mat a x nf
  return a
    
testFmpzi = do
  z <- newFmpzi_ 3 7
  print z
  print $ z*z
  print $ z-z

testQQbar = do
  let n = 2 :: Fmpz
  x <- newQQbar
  withQQbar x $ \x -> do
    withFmpz n $ \n -> 
      qqbar_set_fmpz x n
    qqbar_sqrt x x
    qqbar_print x
    endl
    qqbar_printnd x 16
    endl
  
testAcbPoly = do
  let prec = 1024
      maxIter = 100
  withFmpzPoly (fromList [7, 0, 5, 1]) $ \poly -> do
    withNewAcbPoly $ \cpoly -> do
      acb_poly_set_fmpz_poly cpoly poly prec
      putStrLn "complex polynomial."
      acb_poly_printd cpoly 16
      endl
      degree <- acb_poly_degree cpoly
      roots <- _acb_vec_init degree
      n <- acb_poly_find_roots roots cpoly nullPtr maxIter prec
      putStrLn $ "found " ++ show n ++ " roots:"
      forM_ [0..n-1] $ \j -> do
        acb_printd (roots `advancePtr` fromIntegral j) 16
        endl
      putStrLn "reconstructed polynomial."
      withNewAcbPoly $ \tmp -> do
        acb_poly_product_roots tmp roots n prec
        acb_poly_printd tmp 16
        endl
      _acb_vec_clear roots degree


testAcbHypGeom = do
  let prec = 1024
      maxIter = 100
      poly = hermitePolynomial 7
  print poly
  cpoly <- newAcbPoly
  withFmpzPoly poly $ \poly -> do
    withAcbPoly cpoly $ \cpoly -> do
      withNewAcb $ \z -> do
        acb_poly_set_fmpz_poly cpoly poly prec
        degree <- acb_poly_degree cpoly
        roots <- _acb_vec_init degree
        n <- acb_poly_find_roots roots cpoly nullPtr maxIter prec
        m <- newAcb
        withAcb m $ \m -> do
          acb_set_ui m 7
          forM_ [0..n-1] $ \j -> do
            acb_set z (roots `advancePtr` fromIntegral j)
            acb_printn z 16 arb_str_no_radius
            putStr " -> " 
            acb_hypgeom_hermite_h z m z prec
            acb_printn z 16 arb_str_no_radius
            endl

testBernoulliPoly = do
  let prec = 4096
      maxIter = 200
  withFmpqPoly (bernoulliPolynomial 256) $ \poly -> do
    withNewAcbPoly $ \cpoly -> do
      acb_poly_set_fmpq_poly cpoly poly prec
      degree <- acb_poly_degree cpoly
      roots <- _acb_vec_init degree
      n <- acb_poly_find_roots roots cpoly nullPtr maxIter prec
      putStrLn $ "found " ++ show n ++ " roots:"
      mode <- newCString "w"
      fileName <- newCString "bernoulli_zeros.out"
      out <- fopen fileName mode
      forM_ [0..n-1] $ \j -> do
        let ptr = roots `advancePtr` fromIntegral j
        withNewArb $ \x -> do
          withNewArb $ \y -> do 
            acb_get_real x ptr
            acb_get_imag y ptr
            arb_fprintn out x 16 arb_str_no_radius
            withCString " " $ \s -> fputs s out
            arb_fprintn out y 16 arb_str_no_radius
            withCString "\n" $ \s -> fputs s out
      fclose out
  return ()

bernoulliB n = unsafePerformIO $ do
  b <- newFmpq
  withFmpq b $ \b -> do
    arith_bernoulli_number b $ fromIntegral n
  return b

bernoulliPolynomial n = unsafePerformIO $ do
  poly <- newFmpqPoly
  withFmpqPoly poly $ \poly -> do
    arith_bernoulli_polynomial poly (fromIntegral n)
  return poly

  
testSeries = do
  let prec = 1024
  withNewAcbPoly $ \x -> do
    withNewAcbPoly $ \poly -> do
      acb_poly_one x
      acb_poly_shift_left x x 1
      acb_poly_printd x 16
      endl
      putStrLn "sin series"
      acb_poly_sin_series poly x 32 prec
      acb_poly_printd poly 16
      endl
      result <- newAcb
      withAcb result $ \result -> do
        acb_one result
        acb_poly_evaluate_horner result poly result prec
        putStrLn "series evaluation at 1:"
        acb_printd result 16
        endl
      withAcbRe result $ \r -> do
        arb_printd r 16
        endl
      withAcbIm result $ \r -> do
        arb_printd r 16
        endl
      withNewArb $ \y -> do
        arb_one y
        arb_sin y y prec
        arb_printd y 16
        endl

testAcbModular = do
  x <- newPSL2Z
  withPSL2Z x $ \x -> do
    psl2z_print x
    endl
    CPSL2Z a b c d <- peek x
    fmpz_print a
    endl
    fmpz_print b
    endl
    fmpz_print c
    endl
    fmpz_print d
    endl
    fmpz_set_si a 0
    fmpz_set_si b (-1)
    fmpz_set_si c 1
    fmpz_set_si d 0
    psl2z_print x
    endl
  t <- newPSL2Z_ 1 1 0 1
  s <- newPSL2Z_ 0 (-1) 1 0
  withPSL2Z t psl2z_print
  endl
  withPSL2Z s psl2z_print
  endl

testModular = do
  let i = sqrt (-1 :: CF 1024)
      rho = (1 + i*sqrt 3) / 2
      f z = (modeta z / modeta (7*z)) ^ 4
      fRho = -245/2-sqrt((245/2)^2-2401)
      fI = 7/2*sqrt 7*sqrt(172*sqrt 7 + 455) + 49*sqrt 7 + 245/2
  print $ f rho / fRho
  print $ f i / fI
  -- testLLL (realPart (f rho)) 12

numberOfPartitions n = do
  result <- newFmpz
  withFmpz result $ \result -> do
    partitions_fmpz_ui result n
  return result
  
nextBernoulli = do
  x <- newBernoulliRev 20
  n <- newFmpz
  d <- newFmpz
  replicateM_ 10 $ do
    withBernoulliRev x $ \x -> do
      withFmpz n $ \n -> do
        withFmpz d $ \d -> do
          bernoulli_rev_next n d x
          fmpz_print n
          putStr " "
          fmpz_print d
          endl

testArbHypgeom = do
  fileName <- newCString "flint_test.out"
  mode <- newCString "w"
  cr <- newCString "\n"
  space <- newCString " "
  out <- fopen fileName mode
  let prec = 1024
  withNewArb $ \x -> do
    arb_set_si x (-10)
    withNewArb $ \dx -> do
      arb_set_d dx 0.01
      withNewArb $ \ai -> do
        withNewArb $ \ai' -> do
          withNewArb $ \bi -> do
            withNewArb $ \bi' -> do
              replicateM_ 2000 $ do
                arb_hypgeom_airy ai ai' bi bi' x prec
                -- arb_printn x 16 arb_str_no_radius
                -- putStr " "
                -- arb_printn ai 16 arb_str_no_radius
                -- putStr " "
                -- arb_printn ai' 16 arb_str_no_radius
                -- endl
                arb_fprintn out x 16 arb_str_no_radius
                fputs space out
                arb_fprintn out ai 16 arb_str_no_radius
                fputs space out
                arb_fprintn out ai' 16 arb_str_no_radius
                fputs cr out
                arb_add x x dx prec
  fclose out

-- c file ----------------------------------------------------------------------

foreign import ccall "stdio.h fopen"
  fopen :: CString -> CString -> IO (Ptr CFile)

foreign import ccall "stdio.h fclose"
  fclose :: Ptr CFile -> IO CInt

foreign import ccall "stdio.h fputs"
  fputs :: CString -> Ptr CFile -> IO CInt

--------------------------------------------------------------------------------

testFqPolyFactor = do
  let poly = fromList [1,0,2,2,0,1,1,0,2,2,0,1] :: FmpzPoly
      p = 3 :: Fmpz
  fctx <- newFqCtx p 1 "a"
  foly <- newFqPoly fctx
  f <- newFqPolyFactor fctx
  mtx <- newFmpzModCtx p
  moly <- newFmpzModPoly mtx
  withFqCtx fctx $ \ctx -> do
    withFqPoly foly $ \foly -> do 
      withFmpzModCtx mtx $ \mtx -> do
        withFmpzPoly poly $ \poly -> do
          withFmpzModPoly moly $ \moly -> do
            fmpz_mod_poly_set_fmpz_poly moly poly mtx
            -- fmpz_mod_poly_print moly mtx
            -- endl
            -- withCString "x" $ \x -> do
            --   fmpz_mod_poly_print_pretty moly x mtx
            --   endl
            fq_poly_set_fmpz_mod_poly foly moly ctx
      withCString "x" $ \x -> do
        fq_poly_print_pretty foly x ctx
        endl
      withNewFqPolyFactor fctx $ \f -> do
        withNewFq fctx $ \prefactor -> do
          fq_poly_factor f prefactor foly ctx
          withCString "x" $ \x -> do
            fq_poly_factor_print_pretty f x ctx

testFmpzModPolyFactor = do
  mtx <- newFmpzModCtx 3
  moly <- exFmpzModPoly mtx
  fac <- newFmpzModPolyFactor mtx
  withFmpzModCtx mtx $ \mtx -> do
    withFmpzModPoly moly $ \moly -> do
      withFmpzModPolyFactor fac $ \fac -> do
        fmpz_mod_poly_factor fac moly mtx
        withCString "x" $ \x -> do
          fmpz_mod_poly_factor_print_pretty fac x mtx


testDi = do
  let prec = 16
  withNewArb $ \x -> do
    arb_const_euler x prec
    arb_printn x 32 arb_str_no_radius
    endl
    di_print =<< arb_get_di x
    endl


testFqZech = do
  mtx <- newFmpzModCtx 3
  ctx <- newFqZechCtx 3 1 "a"
  a <- newFqZechMat 3 3 ctx
  poly <- newFqZechPoly ctx
  x <- newFqZech ctx
  moly <- exFmpzModPoly mtx
  withFqZechCtx ctx $ \ftx -> do
    fq_zech_ctx_print ftx
    withFqZech x $ \x -> do
      fq_zech_print x ftx
      endl
    cs <- fq_zech_ctx_get_str ftx
    s <- peekCString cs
    free cs
    print s
    withFqZechMat a $ \a -> do
      fq_zech_mat_print        a ftx
      endl
      fq_zech_mat_print_pretty a ftx
      endl
    withFqZechPoly poly $ \poly -> do
      withFmpzModPoly moly $ \moly -> do
        fq_zech_poly_set_fmpz_mod_poly poly moly ftx
        fq_zech_poly_print poly ftx
        endl
        is_square_free <- fq_zech_poly_is_squarefree poly ftx
        putStrLn $ "polynomial is square free: " ++ show is_square_free

testFqZechRandom = do
 r <- newFRandState
 ctx <- newFqZechCtx 7 4 "a"
 fac <- newFqZechPolyFactor ctx
 pre <- newFqZech ctx
 poly <- newFqZechPoly ctx
 withFRandState r $ \r -> do
   withFqZechCtx ctx $ \ftx -> do
     withFqZechPoly poly $ \poly -> do
       replicateM_ 10 $ do
         fq_zech_poly_randtest poly r 12 ftx
         fq_zech_poly_make_monic poly poly ftx
         is_square_free <- fq_zech_poly_is_squarefree poly ftx
         when (is_square_free == 1) $ do
           withCString "x" $ \var -> do
             fq_zech_poly_print_pretty poly var ftx
             endl
           withFqZechPolyFactor fac $ \fac -> do
             withFqZech pre $ \pre -> do
               fq_zech_poly_factor fac pre poly ftx
               CFqZechPolyFactor _ _ num alloc <- peek fac
               putStrLn $ "num = " ++ show num
               withCString "x" $ \var -> do 
                 fq_zech_poly_factor_print_pretty fac var ftx
                 endl
                 endl
                 fq_zech_poly_factor_print fac ftx
                 endl
           return ()

exFmpzModPoly mtx = do
  let poly = fromList [1,0,2,2,0,1,1,0,2,2,0,1] :: FmpzPoly
  moly <- newFmpzModPoly mtx
  withFmpzModCtx mtx $ \mtx -> do
    withFmpzPoly poly $ \poly -> do
      withFmpzModPoly moly $ \moly -> do
        fmpz_mod_poly_set_fmpz_poly moly poly mtx
  return moly

testBoolMat = do
  a <- newBoolMat 3 5
  withBoolMat a $ \a -> do
    forM_ [0..2] $ \j -> do
      bool_mat_set_entry a j j 1
      bool_mat_set_entry a j (j+2) 1
  print a

testFmpzPolyQ = do
  r <- newFmpzPolyQ
  withFmpzPolyQ r $ \r -> do
    withCString "2  7 1/3  11 0 1" $ \s -> fmpz_poly_q_set_str r s
  print r
  withFmpzPolyQNum r $ \n -> do
    fmpz_poly_print n
    putStr "/"
  withFmpzPolyQDen r $ \d -> do
    fmpz_poly_print d
    endl
  withFmpzPolyQ r $ \r -> do
    fmpz_poly_q_print r
    endl
  -- let p, q :: FmpzPoly
  --     [p, q] = map fromList [[7, 1], [3, 11, 0, 1]] :: [FmpzPoly]
  --     r :: FmpzPolyQ
  --     r = p // q
  -- print r
  print $ numerator r
  print $ denominator r
  return ()

testFmpzMat = do
  let n = 5
  a <- newFmpzMat n n 
  withFmpzMat a $ \a -> do
    withNewFmpz $ \tmp -> do
      forM_ [0..n-1] $ \i -> do
        forM_ [0..n-1] $ \j -> do
          fmpz_set_si tmp ((i+j+1)^4)
          fmpz_mat_set_entry a i j tmp
    fmpz_mat_hnf a a 
  print a
  
testLLL :: forall k. KnownNat k => RF k -> CLong -> IO ()
testLLL r deg = do
  let prec = floatDigits r
      f = 2 ^ prec
      n = deg + 1
      m = n + 1
  lll <- newFmpzLLLDefault
  a <- newFmpzMat n m
  b <- newFmpzMat n m
  poly <- newFmpzPoly
  withFmpzMat a $ \a  -> do
    fmpz_mat_one a
    withFmpzMat b $ \b  -> do
      forM_ [0..n-1] $ \i -> do
        x <- fmpz_mat_entry a i (m-1)
        let tmp = round $ f * r ^ i
        withFmpz tmp $ \tmp -> fmpz_set x tmp
      -- fmpz_mat_print_pretty a
      -- endl
      withFmpzLLL lll $ \lll -> fmpz_lll a b lll
      -- fmpz_mat_print_pretty a
      -- endl
      withFmpzPoly poly $ \poly -> do
        forM_ [0..n-1] $ \j -> do
          x <- fmpz_mat_entry a 0 j
          fmpz_poly_set_coeff_fmpz poly j x
  forM_ (factor poly) $ \(poly, e) -> do 
    poly' <- newArbPoly
    withFmpzPoly poly $ \poly -> do
      withCString "x" $ \var -> do
        fmpz_poly_print_pretty poly var
      withNewArbPoly $ \p -> do
        putStr " -> "
        arb_poly_set_fmpz_poly p poly 1024
        let (RF x) = r
        withNewArb $ \tmp -> do
          withArb x $ \x -> do
            arb_set tmp x
            arb_poly_evaluate tmp p tmp 1024
            arb_abs tmp tmp 
            arb_printn tmp 16 arb_str_no_radius
            endl

testAcbRoots = do
  let prec = 1024
      maxIter = 100
      poly = fromList [1,6,-1,2,0,1] :: FmpzPoly
  print poly
  print $ factor poly
  cpoly <- newAcbPolyFromFmpzPoly poly prec
  withAcbPoly cpoly $ \cpoly -> do
    n <- acb_poly_degree cpoly 
    roots <- _acb_vec_init n
    acb_poly_find_roots roots cpoly nullPtr maxIter prec
    putStrLn "\nroots:\n"
    forM_ [0..n-1] $ \j -> do
      acb_printn (roots `advancePtr` fromIntegral j) 16 arb_str_no_radius
      endl
  return ()

testULong = do
  f <- newNFactor
  withNFactor f $ \f -> do
    n_factor f 60 1
    CNFactor num exp p <- peek f
    factorization <- forM [0..fromIntegral num-1] $ \j -> do
      n <- peek $ exp `advancePtr` j
      x <- peek $ p   `advancePtr` j
      return (x, n)
    print factorization

testULongPrime = do
  let x = 1 :: Fmpz
  withNewNPrimes $ \prime_iter -> do
    replicateM_ 50 $ do
      prime <- n_primes_next prime_iter
      -- print prime
      when (prime < 100) $ do
        withFmpz x $ \x -> do
          fmpz_mul_ui x x prime
        return ()
  print x
  print $ map fst $ factor x
  y <- newFmpz
  withFmpz y $ \y -> fmpz_primorial y 100
  print y
  print $ map fst $ factor y

testEuler :: Fmpz -> Fmpz -> IO Double
testEuler n k = do
  let s :: Fmpq
      s = sum $ map (1//) [1..n]
      r :: RF 1024
      r = fromRational (toRational s) - log (fromIntegral n)
      d = [bernoulliB j / fromIntegral (j*n^j) | j <- [2,4..2*k]]
      result = r + fromRational (toRational (sum d - 1 // (2*n)))
  -- print $ result
  -- print $ result - euler
  return $ toDouble $ result - euler

testFmpzPolyFactor = do
  let poly = fromList [35,24,16,4,1] :: FmpzPoly
      pol = 340282366920938463426481119284349108225 * poly
  print pol
  endl
  print $ factor pol
  endl
  f <- newFmpzPolyFactor
  withFmpzPolyFactor f $ \f -> do
    withFmpzPoly pol $ \pol -> do
      fmpz_poly_factor f pol
      fmpz_poly_factor_print f
      endl

testMediant = do
  let x = 1 // 7
  withFmpq x $ \x -> do
    withNewFmpq $ \r -> do
      withNewFmpq $ \l -> do
        withNewFmpz $ \q -> do
          fmpz_set_ui q 7
          fmpq_farey_neighbors r l x q
          fmpq_print r
          endl
          fmpq_print l
          endl
  return ()

exampleFmpz = do
  x <- newFmpz
  y <- newFmpz
  z <- newFmpz
  withFmpz x $ \x -> do
    withFmpz y $ \y -> do
      withFmpz z $ \z -> do
        fmpz_set_ui x 7
        fmpz_set_ui y 8
        fmpz_mul z x y
        fmpz_print z
        putStr "\n"
        fac <- newFmpzFactor
        withFmpzFactor fac $ \fac -> do
           fmpz_factor fac z
           fmpz_factor_print fac
           putStr "\n"

testFmpqPolyPrint = do
  poly <- newFmpqPoly
  withFmpqPoly poly $ \poly -> fmpq_poly_legendre_p poly 7
  print poly
  let poly = fromList [0, 1] :: FmpqPoly
  withNewFmpqPoly $ \series -> do
    withFmpqPoly poly $ \poly -> do
      fmpq_poly_cos_series series poly 32
      withCString "x" $ \var -> do
        fmpq_poly_print_pretty_as_series series var
        endl
      fmpq_poly_cos_series series poly 32
      fmpq_poly_neg series series
      withCString "x" $ \var -> do
        fmpq_poly_print_pretty_as_series series var
        endl
  return ()

testArbSolve = do
  let prec = 1024
      d :: [[Fmpq]]
      d = [[3, 2, -1], [2, -2, 4], [-1, 1//2, -1]]
      v = [1, -2, 0]
  a <- newArbMat 3 3
  b <- newArbMat 3 1
  x <- newArbMat 3 1
  withArbMat x $ \x -> do
    withArbMat a $ \a -> do
      withArbMat b $ \b -> do
        forM_ [0..2] $ \i -> do
          withFmpq (v!!i) $ \q -> do
            p <- arb_mat_entry b (fromIntegral i) 0
            arb_set_fmpq p q prec
          forM_ [0..2] $ \j -> do
            p <- arb_mat_entry a (fromIntegral i) (fromIntegral j)
            withFmpq ((d !! i) !! j) $ \x -> do 
              arb_set_fmpq p x prec
        arb_mat_solve x a b prec
  print a
  print b
  print x
  return a

testAcbSolve = do
  let prec = 1024
      d :: [[Fmpq]]
      d = [[3, 2, -1], [2, -2, 4], [-1, 1//2, -1]]
      v = [1, -2, 0]
  a <- newAcbMat 3 3
  b <- newAcbMat 3 1
  x <- newAcbMat 3 1
  withAcbMat x $ \x -> do
    withAcbMat a $ \a -> do
      withAcbMat b $ \b -> do
        forM_ [0..2] $ \i -> do
          withFmpq (v!!i) $ \q -> do
            p <- acb_mat_entry b (fromIntegral i) 0
            acb_set_fmpq p q prec
          forM_ [0..2] $ \j -> do
            p <- acb_mat_entry a (fromIntegral i) (fromIntegral j)
            withFmpq ((d !! i) !! j) $ \x -> do 
              acb_set_fmpq p x prec
        acb_mat_solve x a b prec
  print a
  print b
  print x

testPtr = do
  let prec = 1024
      d :: [[Fmpq]]
      d = [[3, 2, -1], [2, -2, 4], [-1, 1//2, -1]]
  q <- newFmpqMat 3 3
  withFmpqMat q $ \q -> do
    forM_ [0..2] $ \i ->
      forM_ [0..2] $ \j -> 
        withFmpq ((d !! i) !! j) $ \x ->
          fmpq_mat_set_entry q (fromIntegral i) (fromIntegral j) x
    CFmpqMat entries r c rows <- peek q
    print rows
    let tmp :: Ptr CFmpq
        tmp = castPtr rows
    print rows
    print entries
  print q
  a <- newAcbMatFromFmpqMat q prec
  b <- newAcbMat 3 3
  withAcbMat b $ \b -> do
    withAcbMat a $ \a -> do
      acb_mat_set b a
      acb_mat_inv b b prec
  print a
  print b

testBernoulliDet n = do
  b <- newFmpqMat n n
  d <- newFmpq
  withFmpqMat b $ \b -> do
    withNewFmpq $ \tmp -> 
      forM_ [0 .. n-1] $ \i ->
        forM_ [0 .. n-1] $ \j -> do
          let k = fromIntegral $ 2*(i+j+1)
          tmp <- zetaRational k
          withFmpq tmp $ \tmp ->
            fmpq_mat_set_entry b i j tmp
          withFmpq d $ \d -> do
            fmpq_mat_det d b
  -- print b
  return $ denominator d
  -- mapM_ print $ factor $ denominator d

bernoulliDet n = do
  withNewFmpz $ \d -> do
    fmpz_one d
    forM_ [1..n] $ \j -> do
      fmpz_mul_ui d d (4*j-1)
      fmpz_mul_ui d d (4*j-3)
      fmpz_mul_ui d d (4*j-3)
      
zetaRational k = do
  (result, _) <- withNewFmpq $ \z -> do
    arith_bernoulli_number z k
    withNewFmpz $ \tmp -> do
      fmpz_fac_ui tmp k
      fmpq_div_fmpz z z tmp
      fmpz_set_ui tmp 2
      fmpz_pow_ui tmp tmp (k-1)
      fmpq_mul_fmpz z z tmp
    fmpq_abs z z 
  return result
  
testST = do
  let n = 32
      x :: Fmpq
      x = read "5530667668905449271708456552/74748754315003247146347079"
  c <- getCF n x
  print x
  putStrLn "\ncontinued fraction decomposition"
  print c
  endl
  g <- getST c
  withPSL2Z g $ \g -> do
    CPSL2Z a b c d <- peek g
    print $ numerator x
    fmpz_print a
    endl
    endl
    print $ denominator x
    fmpz_print c
    endl
    putStrLn "\nmatrix"
    fmpz_print a
    putStr " "
    fmpz_print b
    putStr " "
    fmpz_print c
    putStr " "
    fmpz_print d
    endl
  return ()

getCF n x = do 
  c <- _fmpz_vec_init n
  withFmpq x $ \x -> do
    withNewFmpq $ \rem -> do
      m <- fmpq_get_cfrac_st c rem x n
      return ()
  cf <- forM [0 .. fromIntegral n - 1] $ \j -> do
          tmp <- newFmpz
          withFmpz tmp $ \tmp -> do
            fmpz_set tmp (c `advancePtr` j)
          return tmp
  _fmpz_vec_clear c n
  return $ takeWhile (/=0) cf

getST c = do
  t <- newPSL2Z_ 1 1 0 1
  s <- newPSL2Z_ 0 (-1) 1 0
  let g = mconcat $ map (\n -> t `pow` n <> s) c
  return g

testMember = do
  let n = 12
  u <- _perm_init n
  v <- _perm_init n
  w <- _perm_init n
  p <- _perm_init n
  q <- _perm_init n
  pokeArray u [1,0,3,2,5,4,8,9,6,7,11,10]
  pokeArray v [3,0,9,1,10,2,11,6,4,5,8,7]
  pokeArray w [0,2,4,1,6,7,9,10,11,3,5,8]
  state <- newFRandState
  withFRandState state $ \state -> do
    withNewPSL2Z $ \x -> do
      withNewFmpz $ \k -> do 
        result <- forM [1..10000] $ \j -> do
          psl2z_randtest x state 256
          psl2z_get_perm p u w n x
          withNewPSL2ZWord $ \word -> do
            psl2z_get_word word x
            _perm_set_one q n
            _perm_set_word q u w n word
          m <- peek p
          CPSL2Z a b c d <- peek x
          fmpz_mod_ui k c 6
          p' <- peekArray (fromIntegral n) p
          q' <- peekArray (fromIntegral n) q
          when (p' /= q') $ do
            _perm_print_pretty p n; endl
            _perm_print_pretty q n; endl
            endl
          return (p' == q')
        when (and result) $ do
          putStrLn $ "passed " ++ show (length result) ++ " tests."
          
testMember' = do
  putStrLn "testMember'"
  let n = 12
  u <- _perm_init n
  v <- _perm_init n
  w <- _perm_init n
  p <- _perm_init n
  q <- _perm_init n
  pokeArray u [1,0,3,2,5,4,8,9,6,7,11,10]
  pokeArray v [3,0,9,1,10,2,11,6,4,5,8,7]
  pokeArray w [0,2,4,1,6,7,9,10,11,3,5,8]
  x <- newPSL2Z_ (-452312848583266388373300214947361458987557370876366686577763474145015758847) (-221360937680592961535) 67291784947467583839342053325963375003878788407085294533517086453298069468 32932455181913915357
  withPSL2Z x $ \x -> do
    psl2z_get_perm p u w n x
    putStr "p: "
    _perm_print_pretty p n
    endl
    withNewPSL2ZWord $ \word -> do
      psl2z_get_word word x
      _perm_set_word q u w n word
      putStr "q: "
      _perm_print_pretty q n
      endl
  return ()

sort :: (Ord a) => Vector a -> Vector a
sort x = unsafePerformIO $ do
  v <- Vector.thaw x
  Vector.sort v
  Vector.freeze v

testSort = do
  l <- sample' arbitrary :: IO [Positive Int]
  let v = Vector.fromList $ map getPositive l
  print v
  print $ sort v
  print $ Vector.uniq $ sort v


newtype W = W [Positive Int] deriving Show 
newtype U = U (Vector Int) deriving Show

instance Arbitrary W where
  arbitrary = do
    v <- vector 10
    return $ W v

instance Arbitrary U where
  arbitrary = do
    W x <- arbitrary
    return $ U (Vector.fromList $ map getPositive x)