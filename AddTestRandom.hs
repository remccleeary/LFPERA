module AddTestRandom where


import Blocks(Block(ZeroBlock,Block),Digit(X,Z),Sign(Plus,Minus))
import FD(doubleToFD,twoFDDiv)
import Floating
import Data.List
import Data.Ratio
import Test.QuickCheck hiding (getSize)
import System.Random
import Control.Monad (replicateM)







threeAdd :: (Show a, Floats a) => a -> a -> a -> (a,a,a)
threeAdd ia ib ic = 
   let(a:b:c:[]) = sortBy negFloatCompare [ia,ib,ic] in 
   let(s1,e1) = twoSumRN b c in
   let(temp1,e2) = twoSumRN a s1 in
   let(temp2,temp3) = twoSumRN e1 e2 in
   let(out1,ttemp2) = twoSumRN temp1 temp2 in
   let(out2,out3) = twoSumRN ttemp2 temp3 in
   (out1,out2,out3)


getDigits :: Int -> [[Digit]]
getDigits n = map (X:) (getDigitsRec (n-1))


getDigitsRec  :: Int -> [[Digit]]
getDigitsRec 0 =  [[]]
getDigitsRec n =  map (Z:) bss ++ map (X:) bss
  where bss = getDigitsRec (n - 1) 



--Only works on finite [a]
removeZeros :: (Show a, Floats a) => [a] -> [a]
removeZeros [] = []
removeZeros (a:as) =
  if(isZero a) then
    (removeZeros as)
  else a:(removeZeros as)

--Only works on finite [a]
priestAdd :: (Show a, Floats a) => [a] -> [a] -> ([a],Integer)
priestAdd as bs =
  let(l1,c1) = priestAddNonNorm as bs in
    let (l2,c2) = priestRenorm l1 in
      (l2,c1 + c2)

priestAddNonNorm :: (Show a, Floats a) => [a] -> [a] -> ([a],Integer)
priestAddNonNorm as bs =
  let(l,c) = (priestAddStep1 (reverse as) (reverse bs)) in
    let l2 = (removeZeros(reverse l)) in
      (l2,c)

priestAddStep1 :: (Show a, Floats a) => [a] -> [a] -> ([a],Integer)
priestAddStep1 [] bs  = (bs,0)
priestAddStep1 as []  = (as,0)
priestAddStep1 (a:as) (b:bs)  =
  if(dominate a b) then
    let(l,c) = (priestAddStep1 (a:as) bs) in
      ((b:l),c)
  else
    if(dominate b a) then
      let (l,c) = (priestAddStep1 as (b:bs)) in
        ((a:l),c)
    else
      priestAddStep2 as bs a b 0

priestAddStep2 :: (Show a, Floats a)
  =>[a] -> [a] -> a -> a -> Integer -> ([a],Integer)
priestAddStep2 [] [] a b c =
  let(s,e) = twoSumRN a b in (([e,s]),(c+1))
priestAddStep2 (na:as) [] a b c =
  let(s,e) = twoSumRN a b in
    let nna = s in
      let nnb = na in
        let(l,nc) = (priestAddStep2 as [] nna nnb (c+1)) in
        ((e:l),(nc))
priestAddStep2 [] (nb:bs) a b c=
  let(s,e) = twoSumRN a b in
    let nna = s in
      let nnb = nb in
        let(l,nc) = (priestAddStep2 [] bs nna nnb (c+1)) in
        ((e:l),(nc))
priestAddStep2 (na:as) (nb:bs) a b c =
  let(s,e) = twoSumRN a b in
    let nna = s in
      if(expGreater na nb) then
        let nnb = nb in
          let(l,nc) = (priestAddStep2 (na:as) bs nna nnb (c+1)) in
             ((e:l),nc)
       else
        let nnb = na in
          let(l,nc) = (priestAddStep2 as (nb:bs) nna nnb (c+1)) in
           ((e:l),nc)




priestRenorm ::  (Show a, Floats a) => [a] -> ([a],Integer)
priestRenorm [] = ([],0)
priestRenorm as =
  let ((f:fs),c1) = sweepUp as in
    let (l1,c2) = priestRenorm fs in
      let l2 = removeZeros l1 in
        let (l3,c3) = sweepDown l2 in
          (f:(l3),(c1+c2+c3))


sweepUp :: (Show a, Floats a) => [a] -> ([a],Integer)
sweepUp [] = ([],0)
sweepUp as =
  let (ra:ras) =  reverse as in
    let(l,c) = sweepUpRec ras ra 0 in
     ((reverse l), c)

sweepUpRec :: (Show a, Floats a) => [a] -> a -> Integer -> ([a],Integer)
sweepUpRec [] b c = ([b],c)
sweepUpRec (a:as) b c =
  let(s,e) = twoSumRN a b in
    let(l,nc) = sweepUpRec as s (c+1) in
      ((e:l),nc)

sweepDown :: (Show a, Floats a) => [a] -> ([a],Integer)
sweepDown [] = ([],0)
sweepDown (a:as) = sweepDownRec as a 0

sweepDownWC :: (Show a, Floats a) => [a] -> Integer -> ([a],Integer)
sweepDownWC [] c = ([],c)
sweepDownWC (a:as) c = sweepDownRec as a c


sweepDownRec :: (Show a, Floats a) => [a] -> a -> Integer ->  ([a],Integer)
sweepDownRec [] b c = ([b],c)
sweepDownRec (a:as) b c =
  let(s,e) = twoSumRN a b in
    let(l,c1) =
         if(isZero e) then
           (sweepDownWC as (c+1))
         else
           sweepDownRec as e (c+1)
    in
      (s:l,c1)



isSafe :: (Show a, Floats a) => a -> [a] -> [a] -> [a]-> a ->  Bool
isSafe out [] [] [] prev = not (expGreater prev out) 
isSafe out [] [] (e:es) prev =
  not (expGreater prev out) && (expGreaterBy (getSize e) out e)
isSafe out fs [] es prev = isSafe out fs fs es prev
isSafe out [] gs es prev = isSafe out gs gs es prev
isSafe out fs gs [] prev = isSafe out fs gs gs prev
isSafe out (f:fs) (g:gs) (e:es) prev =
  let k = (getSize out) in
    (expGreaterBy (2*k + 3) out f) &&
    (expGreaterBy (2*k + 3) out g) &&
    (not (expGreater prev out))    &&
    (expGreaterBy k out e)


  
add :: (Show a, Floats a) => [a] -> [a] -> [(a,Integer)]
add [] gs = addCountToZBCL gs 0
add fs [] = addCountToZBCL fs 0
add (f:fs) (g:gs) = 
  let (bound) = max (getExp f) (getExp g) + 3 in
  let (s,e) = twoSumRN f g in
  addRec fs gs [s,e] bound 1

addCountToZBCL :: [a] -> Integer -> [(a,Integer)]
addCountToZBCL [] _ = []
addCountToZBCL (a:as) c = (a,c):(addCountToZBCL as c)

addRec :: (Show a,Floats a) => [a] -> [a] -> [a] -> Integer ->  Integer -> [(a,Integer)]
addRec [] [] es i c = (addCountToZBCL es c)
addRec fs [] [] i c = (addCountToZBCL fs c)
addRec [] gs [] i c = (addCountToZBCL gs c)
addRec fs [] (e:es) bound c = (e,c):(addRec fs es [] ((getExp e) - (getSize e)) c)
addRec [] gs (e:es) bound c = (e,c):(addRec gs es [] ((getExp e) - (getSize e)) c)
addRec (f:fs) (g:gs) [] bound c = 
  let (s,e) = twoSumRN f g in
  addRec fs gs [s,e] bound (c+1)
addRec (f:fs) (g:gs) (prev:es) bound c = 
  if(bound > (getExp prev) + (getSize prev) + 2) then 
    let zero =  (createZero (getSize prev) bound) in
    if(isSafe zero (f:fs) (g:gs) (prev:es) prev) then 
      (zero,c):
      (addRec (f:fs) (g:gs) (prev:es) (bound - (getSize prev)) c) 
    else 
      let (out,nPrev,e) = threeAdd prev f g  in 
      let (nes,pc) = priestAdd es [out,nPrev,e] in
      (addRec (fs) (gs) (nes) bound (c+5+pc)) 
  else
    let (out,nPrev,e) = threeAdd prev f g  in 
    let (nes,pc1) = priestAdd es [nPrev,e] in
      if(isSafe out fs gs nes prev) then
        (out,(c+pc1+5)):
        (addRec fs gs nes ((getExp out) - (getSize out)) (c+pc1+5))
      else
        let (nnes,pc2) = priestAdd [out] nes in 
          addRec fs gs nnes bound (c+pc1+pc2+5)





addTester1 :: [[FDWrap]] -> [[FDWrap]] -> [[(FDWrap,Integer)]]
addTester1 [] bs = []
addTester1 (a:as) (bs) = (addTester2 a bs) ++ (addTester1 as bs)

addTester2 :: [FDWrap] -> [[FDWrap]] -> [[(FDWrap,Integer)]]
addTester2 a [] = []
addTester2 a (b:bs) = 
  let as = add a b in
    as:(addTester2 a bs)
       

dropZBCL :: [(FDWrap,Integer)] -> [Integer]
dropZBCL [] = []
dropZBCL ((b,i):rest) = i:(dropZBCL rest)

twoSumCounts :: [[(FDWrap,Integer)]] -> [[Integer]]
twoSumCounts [] = []
twoSumCounts (a:as) = (toLengthFour (dropZBCL a)):(twoSumCounts as)


toLengthFour :: [Integer] -> [Integer]
toLengthFour as =
  if(length as < 4) then
    as ++ (padBackWithLast (last as) (4 - (length as)))
  else
    (take 4 as)


padBackWithLast :: Integer -> Int -> [Integer]
padBackWithLast i 0 = []
padBackWithLast i n = i:(padBackWithLast i (n-1))


getNthBlock :: Int -> [[Integer]] -> [Integer]
getNthBlock n [] = []
getNthBlock n (a:as) = (a !! n):(getNthBlock n as)

sumList :: [Integer] -> Integer
sumList [] = 0
sumList (a:as) = a + (sum as)

average :: [Integer] -> Double
average l = (fromIntegral (sumList l))/(fromIntegral (length l))


averagesOfEach4 :: [[(FDWrap,Integer)]] -> [Double]
averagesOfEach4 tests =
  let all = twoSumCounts tests in
    let b1 = getNthBlock 0 all in
      let b2 = getNthBlock 1 all in
        let b3 = getNthBlock 2 all in
          let b4 = getNthBlock 3 all in
            [average b1, average b2, average b3, average b4]
            
          
randomColist :: Double -> Double -> IO [Double]
randomColist a b = do
  g <- newStdGen
  return (randomRs (a,b) g)

randomSignsCoList :: IO [Bool]
randomSignsCoList = do
  g <- newStdGen
  return (randomRs (True,False) g)
  
randomDoubles = randomColist 0.5 1.0

createZBL :: Integer -> [Double] -> [Bool] -> [FDWrap]
createZBL exp [] [] = []
createZBL exp (d:ds) (b:bs) =
  let nd = (if(b) then d else -d) in
    (wrapFD(exp, nd)):(createZBL (exp - 53) ds bs)

createZBLS :: Int -> [Double] -> [Bool] -> [[FDWrap]]
createZBLS _ [] [] = []
createZBLS size randomDouble randomSign =
  let head = createZBL 0 (take size randomDouble) (take size randomSign) in
    head:(createZBLS size (drop size randomDouble) (drop size randomSign))


main :: Int -> Int  -> IO()
main size tests  = do
  randomDoubles <- randomColist 0.5 1.0 --(creates random doubles with exponent of 0)
  randomSigns <- randomSignsCoList
  let doubles = take (size * tests) randomDoubles 
  let signs = take (size * tests) randomSigns 
  let zbls = createZBLS size doubles signs 
  let tests = addTester1 zbls zbls
  print (length tests)
  let avgs = averagesOfEach4 tests
  print avgs
  






