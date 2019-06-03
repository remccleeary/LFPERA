module FCL where


import Blocks(Block(ZeroBlock,Block),Digit(X,Z),Sign(Plus,Minus))
import FD(doubleToFD,twoFDDiv)
import Floating
import Data.List
import Data.Ratio
import Test.QuickCheck hiding (getSize)
import System.Random
import Control.Monad (replicateM)





--Approx allows us to get the rational value of a finite prefix
approx :: (Show a, Floats a) =>  [a] -> Integer -> Rational
approx [] n = 0%1
approx b 0 = 0%1
approx (b:bs) n = (toRat b) + (approx bs (n-1))





threeAdd :: (Show a, Floats a) => a -> a -> a -> (a,a,a)
threeAdd ia ib ic = 
   let(a:b:c:[]) = sortBy negFloatCompare [ia,ib,ic] in 
   let(s1,e1) = twoSumRN b c in
   let(temp1,e2) = twoSumRN a s1 in
   let(temp2,temp3) = twoSumRN e1 e2 in
   let(out1,ttemp2) = twoSumRN temp1 temp2 in
   let(out2,out3) = twoSumRN ttemp2 temp3 in
   (out1,out2,out3)



--Only works on finite [a]
removeZeros :: (Show a, Floats a) => [a] -> [a]
removeZeros [] = []
removeZeros (a:as) = if(isZero a) then (removeZeros as) else a:(removeZeros as)

--Only works on finite [a]
priestAdd :: (Show a, Floats a) => [a] -> [a] -> [a]
priestAdd as bs = priestRenorm(priestAddNonNorm as bs)

priestAddNonNorm :: (Show a, Floats a) => [a] -> [a] -> [a]
priestAddNonNorm as bs =(removeZeros(reverse (priestAddStep1 (reverse as) (reverse bs))))

priestAddStep1 :: (Show a, Floats a) => [a] -> [a] -> [a]
priestAddStep1 [] bs = bs
priestAddStep1 as [] = as
priestAddStep1 (a:as) (b:bs) =
  if(dominate a b) then b:(priestAddStep1 (a:as) bs) else
    if(dominate b a) then a:(priestAddStep1 as (b:bs)) else
      priestAddStep2 as bs a b

priestAddStep2 :: (Show a, Floats a) => [a] -> [a] -> a -> a -> [a]
priestAddStep2 [] [] a b = let(s,e) = twoSumRN a b in [e,s]
priestAddStep2 (na:as) [] a b =
  let(s,e) = twoSumRN a b in
    let nna = s in
      let nnb = na in
        e:(priestAddStep2 as [] nna nnb)
priestAddStep2 [] (nb:bs) a b =
  let(s,e) = twoSumRN a b in
    let nna = s in
      let nnb = nb in
        e:(priestAddStep2 [] bs nna nnb)
priestAddStep2 (na:as) (nb:bs) a b =
  let(s,e) = twoSumRN a b in
    let nna = s in
      if(expGreater na nb) then
        let nnb = nb in e:(priestAddStep2 (na:as) bs nna nnb)
       else
        let nnb = na in e:(priestAddStep2 as (nb:bs) nna nnb)

priestRenorm :: (Show a, Floats a) => [a] -> [a]
priestRenorm [] = []
priestRenorm as =
  let (f:fs) = sweepUp as in
    f:(sweepDown (removeZeros (priestRenorm fs)))

sweepUp :: (Show a, Floats a) => [a] -> [a]
sweepUp [] = []
sweepUp as = let (ra:ras) =  reverse as in reverse(sweepUpRec ras ra)

sweepUpRec :: (Show a, Floats a) => [a] -> a -> [a]
sweepUpRec [] b = [b]
sweepUpRec (a:as) b = let(s,e) =  twoSum a b in e:(sweepUpRec as s)

sweepDown :: (Show a, Floats a) => [a] -> [a]
sweepDown [] = []
sweepDown (a:as) = sweepDownRec as a

sweepDownRec :: (Show a, Floats a) => [a] -> a -> [a]
sweepDownRec [] b = [b]
sweepDownRec (a:as) b = let(s,e) =  twoSum a b in
  if(isZero e) then s:(sweepDown as) else s:(sweepDownRec as e)


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


--Addition removes first 0 if it exists
addition :: (Show a, Floats a) => [a] -> [a] -> [a]
addition [] gs = gs
addition fs [] = fs
addition fs gs = 
  let sum = add fs gs in
  if(null sum) then sum else
    let(high:rest) = sum in
    if(isZero high) then rest else high:rest
  
add :: (Show a, Floats a) => [a] -> [a] -> [a]
add [] gs = gs
add fs [] = fs
add (f:fs) (g:gs) = 
  let (bound) = max (getExp f) (getExp g) + 3 in
  let (s,e) = twoSumRN f g in
  addRec fs gs [s,e] bound

addRec :: (Show a,Floats a) => [a] -> [a] -> [a] -> Integer ->  [a]
addRec [] [] es _ = es
addRec fs [] [] _ = fs
addRec [] gs [] _ = gs
addRec fs [] (e:es) bound = e:(addRec fs es [] ((getExp e) - (getSize e)))
addRec [] gs (e:es) bound = e:(addRec gs es [] ((getExp e) - (getSize e)))
addRec (f:fs) (g:gs) [] bound = 
  let (s,e) = twoSumRN f g in
  addRec fs gs [s,e] bound
addRec (f:fs) (g:gs) (prev:es) bound = 
  if(bound > (getExp prev) + (getSize prev) + 2) then 
    let zero =  (createZero (getSize prev) bound) in
    if(isSafe zero (f:fs) (g:gs) (prev:es) prev) then 
      zero:(addRec (f:fs) (g:gs) (prev:es) (bound - (getSize prev))) 
    else 
      let (out,nPrev,e) = threeAdd prev f g  in
      let nes = priestAdd es [out,nPrev,e] in
      (addRec (fs) (gs) (nes) bound) 
  else
    let (out,nPrev,e) = threeAdd prev f g  in 
    let nes = priestAdd es [nPrev,e] in
      if(not (isSafe out fs gs nes prev)) then 
        let nnes = priestAdd [out] nes in 
        addRec fs gs nnes bound 
      else
          out:(addRec fs gs nes ((getExp out) - (getSize out)))
        
 
negation :: (Show a, Floats a) => [a] -> [a]
negation [] = []
negation (a:rest) = (Floating.negate a):(negation rest)

minus :: (Floats a, Show a) => [a] -> [a] -> [a]
minus as bs = add as (negation bs)    



infiniteSum :: (Show a, Floats a) => [[a]] -> [a]
infiniteSum as = let(sum) = infSum as in
  if(null sum) then sum else
    let(high:rest) = sum in
    if(isZero high) then rest else sum


infSum :: (Show a, Floats a) => [[a]] -> [a]
infSum [] = []
infSum (as:[]) = as
infSum (as:bs:rest) =
  let nprevs = addition as bs in
    infSumRec rest nprevs (getExp (head as) + (getSize (head as)) + 1)


infSumRec :: (Show a, Floats a) => [[a]] ->  [a] -> Integer -> [a]
infSumRec [] prevs _ = prevs
infSumRec (as:[]) prevs _ = addition as prevs
infSumRec (as:rest) [] bound = infSumRec rest as bound
infSumRec (as:bs:rest) (prev:prevs) bound = 
  if(bound > (getExp prev) + (getSize prev) + 2) then 
    let zero =  (createZero (getSize prev) bound) in
    if(isSafe zero as bs bs prev) then
      zero:(infSumRec (as:bs:rest) (prev:prevs) (getExp zero - getSize zero))
    else 
      let nPrevs = addition as (prev:prevs) in
      (infSumRec (bs:rest) nPrevs bound) 
  else
    let sum = addition (prev:prevs) as in
    if (null sum) then infSumRec rest bs bound else
      let(high:highs) = sum in
      if(isZero high) then infSumRec (bs:rest) highs bound else
        if(isSafe high bs bs bs prev) then
          high:(infSumRec (bs:rest) highs ((getExp high) - (getSize high)))
        else
          infSumRec (bs:rest) (high:highs) bound

   
   
multiply :: (Show a, Floats a) => [a] -> [a] -> [a]
multiply [] x = []
multiply x [] = []
multiply (a:[]) bs = singleMult a bs
multiply as (b:[]) = singleMult b as
multiply (a:as) (b:bs) = 
  let((na:nas),aShift) = shiftDown (a:as) in
  let((nb:nbs),bShift) = shiftDown (b:bs) in
  shiftUp (aShift + bShift) (mult (na:nas) (nb:nbs))
  

-- for ZBCL's in -1 to 1
mult :: (Show a, Floats a) => [a] -> [a] -> [a]
mult [] x = []
mult x [] = []
mult as bs =  infiniteSum (infSumMultHelper as bs)

        
infSumMultHelper :: (Show a, Floats a) =>  [a] -> [a] -> [[a]]
infSumMultHelper [] gs = []
infSumMultHelper fs [] = []
infSumMultHelper (f:fs) (g:gs) = (singleMult f (g:gs)):(infSumMultHelper fs (g:gs)) 
          
singleMult :: (Show a, Floats a) => a -> [a] -> [a]
singleMult f gs = infiniteSum(singleMultHelper f gs)

singleMultHelper :: (Show a, Floats a) => a -> [a] -> [[a]]
singleMultHelper f [] = []
singleMultHelper f (g:gs) = let(s,e) = twoMult f g in ([s,e]):(singleMultHelper f gs)




divide :: (Show a, Floats a) => [a] -> [a] -> [a]
divide fs [] = error "Divide by Zero"
divide [] gs = []
divide fs gs = 
  let(shift) = shiftUpToTwo gs in
  FCL.div (shiftUp shift fs) (shiftUp shift gs)
  
shiftUpToTwo :: (Show a, Floats a) =>  [a] -> Integer 
shiftUpToTwo (a:as) = if (getExp a) < 1 then 1 - (getExp a) else 0

div :: (Show a, Floats a) => [a] -> [a] -> [a]
div [] gs = []
div fs gs = infiniteSum (divideHelper fs gs)

divideHelper :: (Show a, Floats a) => [a] -> [a] -> [[a]]
divideHelper fs [] = []
divideHelper [] gs = []
divideHelper fs (g:gs) = 
  if(isZero g) then [g]:(divideHelper fs gs) else
    (singleDiv fs g):(divideHelper (negation (multiply fs gs)) (singleMult g (g:gs)))

singleDiv :: (Show a, Floats a) =>  [a] -> a -> [a]
singleDiv fs g = infiniteSum (singleDivHelper fs g)

singleDivHelper :: (Show a, Floats a) =>  [a] -> a -> [[a]]
singleDivHelper [] g = []
singleDivHelper (f:fs) g = 
    (twoDivFCL f g):(singleDivHelper fs g)

twoDivFCL :: (Show a, Floats a) => a -> a -> [a]
twoDivFCL x y = 
  if(isZero x) then [createZero (getSize x) (getExp x - getExp y)] else
  let (a,b) = twoDiv x y in (a:(twoDivFCL b y))



pow :: (Show a, Floats a) => [a] -> Integer -> Integer -> [a]
pow as 0 size = (intToFloat 1 size)
pow as 1 size = as
pow as n size = multiply as (pow as (n-1) size)


finiteSum :: (Show a, Floats a) => [[a]] -> [a]
finiteSum [] = []
finiteSum (as:rest) = addition as (finiteSum rest)



bppPi :: (Show a, Floats a) => Integer -> [a] 
bppPi size = infSum (bppPiHelper size 0)


bppPiHelper ::(Show a, Floats a) => Integer -> Integer -> [[a]]
bppPiHelper size k =
  (multiply
   (divide
    (intToFloat 1 size)
    (pow (intToFloat 16 size) k size)
   )
   (bppPiHelperP2 size k)
  ):(bppPiHelper size (k+1))


bppPiHelperP2 :: (Show a, Floats a) => Integer -> Integer -> [a]
bppPiHelperP2 size k =
  finiteSum [(divide
              (intToFloat 4 size)
              (addition
               (mult (intToFloat 8 size) (intToFloat k size))
               (intToFloat 1 size)
              )
             ),
             (negation
              (divide
               (intToFloat 2 size)
               (addition
                (multiply
                 (intToFloat 8 size)
                 (intToFloat k size)
                )
                (intToFloat 4 size)
               )
              )
             ),
             (negation
              (divide (intToFloat 1 size)
               (addition
                (multiply
                 (intToFloat 8 size)
                 (intToFloat k size)
                )
                (intToFloat 5 size)
               )
              )
             ),
             (negation
              (divide
               (intToFloat 1 size)
               (addition
                (multiply
                 (intToFloat 8 size)
                 (intToFloat k size)
                )
                (intToFloat 6 size)
               )
              )
             )]










