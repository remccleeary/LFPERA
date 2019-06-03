module Blocks where

import Data.List
import Data.Ratio
import Data.Tuple


import Test.QuickCheck hiding (getSize)


data Digit = Z | X deriving (Show,Read,Eq)

data Sign = Plus | Minus deriving (Show,Read,Eq)

data Block = ZeroBlock (Integer) (Integer)
  | Block (Integer) (Integer) (Sign) ([Digit])
  deriving (Show,Read)

instance Eq Block where 
  b1 == b2 =
    (blockToRational b1) == (blockToRational b2)
  

instance Ord Block where
   b1 <= b2 =
     (abs (blockToRational b1)) <= (abs (blockToRational b2))

blockToRational :: Block -> Rational
blockToRational (ZeroBlock _ _)  =
  0 % 1
blockToRational (Block (s)(e)(Plus)(l)) =
  blockToRationalHelper e l
blockToRational (Block (s)(e)(Minus)(l)) =
  -1 * blockToRationalHelper e l


blockToRationalHelper :: Integer -> [Digit] -> Rational
blockToRationalHelper  e [] =
  0 % 1
blockToRationalHelper  e (X : t) =
  if (e >= 0) then
    (1 * 2^e)%1 + blockToRationalHelper (e-1) t
  else
    1%(1 * 2^(e * (-1))) + blockToRationalHelper (e-1) t
blockToRationalHelper  e (Z : t) =
  blockToRationalHelper (e-1) t


   

createZeroBlock :: Integer -> Integer -> Block
createZeroBlock s e = ZeroBlock s e

isBlockZero :: Block -> Bool
isBlockZero a = (a == (ZeroBlock 0 1))
   
dominateB :: Block -> Block -> Bool
dominateB f g = 
  let(s,e) = twoSumWithBPB f g in
  f == s


expGreaterB :: Block -> Block -> Bool
expGreaterB f g = 
  let e1 = getExpB f in
  let e2 = getExpB g in
  e1 > e2


expGreaterByB :: Block -> Block -> Integer -> Bool
expGreaterByB f g i = 
  let e1 = getExpB f in
  let e2 = getExpB g in
  e1 - i >= e2


negateBlock :: Block -> Block
negateBlock (ZeroBlock s e) = ZeroBlock s e
negateBlock (Block s e sn l) = (Block s e (opp sn) l)


twoSumB :: Block -> Block -> (Block,Block)
twoSumB a b = let(s,e) = (if(a >= b) then twoSumN a b else twoSumN b a) in
   ((checkZero s),e)

checkZero :: Block -> Block
checkZero (ZeroBlock s e) = ZeroBlock s e
checkZero (Block a b c ds) = if(allZs ds) then (ZeroBlock a (b+a)) else (Block a b c ds)

allZs :: [Digit] -> Bool
allZs [] = True
allZs (d : ds) = (d == Z) && (allZs ds)

hasZ :: [Digit] -> Bool
hasZ [] = False
hasZ (d : ds) = (d == Z) || (hasZ ds)


twoSumN :: Block -> Block -> (Block, Block)
twoSumN b (ZeroBlock s i) =
  if(i > ((getExpB b) + (getSizeOfBlock b))) then
    ((ZeroBlock s i), b)
  else
    (b,(ZeroBlock s ((getExpB b) - s)))
twoSumN (ZeroBlock s i) b =
  if(i > ((getExpB b) + (getSizeOfBlock b))) then
    ((ZeroBlock s i), b)
  else
    (b,(ZeroBlock s ((getExpB b) - s)))
twoSumN (Block sz1 e1 s1 l1) (Block sz2 e2 s2 l2) =
  if((e1 - e2) < sz1) then
    twoSumHelper sz1 (Block sz1 e1 s1 l1) (Block sz2 e2 s2 l2)
  else
    ((Block sz1 e1 s1 l1),(Block sz2 e2 s2 l2))

getSize :: [a] -> Integer
getSize [] = 0
getSize (h : t) = 1 + getSize(t)

twoSumHelper :: (Integer) -> Block -> Block -> (Block,Block)
twoSumHelper (size) (Block sz1 e1  s1  l1) (Block sz2 e2 s2 l2) = 
  let expDif = e1 - e2 in 
    let overlap = size - expDif in 
      let nl1 = padBack l1 (size - overlap) in
        let nl2 = padFront l2 (size - overlap) in 
         if (s1 == s2) then
           (let sum = boolSum nl1 nl2 in
            let sizeSum = getSize sum in 
             let e1Up = sizeSum > size + (size - overlap) in 
              splitBlocks sum size e1 e1Up s1)
           else
           (let sum = boolSubt nl1 nl2 in
              splitBlocks sum size e1 False s1)

splitBlocks ::
  [Bool] -> Integer -> Integer -> Bool -> Sign -> (Block,Block) 
splitBlocks l size e1 e1Up sign =
  let (nl,edown) = getLeadingOne l 0 in
    let (fb,lo,ee) = getFirstBlock nl size (e1-edown) e1Up sign  in
      let lb = getLastBlock lo size ee sign in (fb,lb)

getFirstBlock ::
  [Bool] -> Integer -> Integer -> Bool -> Sign -> (Block, [Bool], Integer)
getFirstBlock l s e1 e1Up sign =
  let (b1,b2) = getBitVect l s in
    if(e1Up) then
      ((Block s (e1 + 1) sign (boolToDigit(b1))), b2, (e1+1 - s))
    else
      ((Block s e1 sign (boolToDigit(b1))), b2, (e1 - s))

getLeadingOne :: [Bool] -> Integer -> ([Bool],Integer)
getLeadingOne [] n = ([],n)
getLeadingOne (True : t) n = ((True : t), n)
getLeadingOne (False : t) n = getLeadingOne t (n+1)
                                                                     
getBitVect :: [Bool] -> Integer -> ([Bool],[Bool])
getBitVect r 0 = ([], r)
getBitVect [] n = ((getFalses n),[])
getBitVect (h:t) n =
  let (start,end) = getBitVect t (n-1) in ((h:start),end)

getLastBlock :: [Bool] -> Integer -> Integer -> Sign -> Block
getLastBlock (False : t) s e sign =
  getLastBlock t s (e - 1) sign
getLastBlock (True : t) s e sign =
  let b1 = getBitVect2 (True : t) s in
    (Block s e sign (boolToDigit(b1)))
getLastBlock [] s e sign = (ZeroBlock s e)

getBitVect2 :: [Bool] -> Integer  -> [Bool]
getBitVect2 [] n = getFalses (n) 
getBitVect2 l 0 = []
getBitVect2 (e : t) n = e : (getBitVect2 t (n-1))

getFalses :: Integer -> [Bool]
getFalses 0 = []
getFalses n = False:(getFalses (n-1))
                        
padFront :: [Digit] -> Integer -> [Bool]
padFront l 0 = digitToBool l
padFront l n = False : padFront l (n-1)

digitToBool :: [Digit] -> [Bool]
digitToBool [] = []
digitToBool (X : t) = True : digitToBool t
digitToBool (Z : t) = False : digitToBool t

boolToDigit :: [Bool] -> [Digit]
boolToDigit [] = []
boolToDigit (True : t) = X : boolToDigit t
boolToDigit (False : t) = Z : boolToDigit t

padBack :: [Digit] -> Integer -> [Bool]
padBack l i = (digitToBool l) ++ padBackHelper i

padBackHelper :: Integer -> [Bool]
padBackHelper 0 = []
padBackHelper n = False : padBackHelper (n - 1)

boolSum :: [Bool] -> [Bool] -> [Bool]
boolSum x y = reverse(boolSumWithCarry (reverse x) (reverse y) False)

boolSumWithCarry :: [Bool] -> [Bool] -> Bool -> [Bool]
boolSumWithCarry [] [] True = [True]
boolSumWithCarry [] [] False = []
boolSumWithCarry [] y c =
  boolSumWithCarry ([False]) y c
boolSumWithCarry x [] c =
  boolSumWithCarry x ([False]) c
boolSumWithCarry (False : xs) (False : ys) False =
  False : (boolSumWithCarry xs ys False)
boolSumWithCarry (True : xs) (False : ys) False =
  True : (boolSumWithCarry xs ys False)
boolSumWithCarry (False : xs) (True : ys) False =
  True : (boolSumWithCarry xs ys False)
boolSumWithCarry (True : xs) (True : ys) False =
  False : (boolSumWithCarry xs ys True)
boolSumWithCarry (False : xs) (False : ys) True =
  True : (boolSumWithCarry xs ys False)
boolSumWithCarry (True : xs) (False : ys) True =
  False : (boolSumWithCarry xs ys True)
boolSumWithCarry (False : xs) (True : ys) True =
  False : (boolSumWithCarry xs ys True)
boolSumWithCarry (True : xs) (True : ys) True =
  True : (boolSumWithCarry xs ys True)

boolComplement :: [Bool] -> [Bool] 
boolComplement [] = []
boolComplement (True : t) =
  (False : (boolComplement t))
boolComplement (False : t) =
  (True : (boolComplement t))

boolSubt :: [Bool] -> [Bool] -> [Bool]
boolSubt x y =
  Data.List.tail(boolSum (x) (boolSum [True] (boolComplement y)))


getSingleList :: Integer -> [Digit]
getSingleList 0 = []
getSingleList n = Z : getSingleList(n-1)

opp :: Sign -> Sign
opp Plus = Minus
opp Minus = Plus

getSecondBlock :: Integer -> Integer -> Sign -> [Digit] -> Block
getSecondBlock size exp sign l =
  (Block size (exp-size+1) (opp sign) (X:(getSingleList(size-1))))

lastTwo :: [Digit] -> Integer -> Integer -> [Digit]
lastTwo (h:t) size count =
  if(size - count > 3) then lastTwo t size (count + 1) else t

getNewList :: Integer -> Integer -> [Digit] -> (Integer, [Digit])
getNewList size exp (X : X : []) =
  ((exp - (size - 1)), (X : getSingleList(size-1)))
getNewList size exp (X : Z : []) =
  ((exp - (size - 2)), (X : getSingleList(size-1)))
getNewList size exp (Z : X : []) =
  ((exp - (size - 2)), (X : X : getSingleList(size-2)))




checkList :: [Digit] ->  Bool
checkList []  = True
checkList (X : t) = checkList t
checkList (Z : t) = False

sparseBl :: [Block] -> [Block]
sparseBl [] = []
sparseBl ((ZeroBlock _ _):y) =
  sparseBl y
sparseBl (x:y) =
  if(x == (ZeroBlock 0 1)) then sparseBl y else x:(sparseBl y)


zeroOverlapB :: [Block] -> [Block]
zeroOverlapB l =
  sparseBl (sweepDownB (reverse (sparseBl (zeroOverlapBRec (sort l)))))

simpleMergeB :: Block -> [Block] -> [Block]
simpleMergeB a [] = [a]
simpleMergeB a (b:bs) =
  if(expGreaterB a b) then
    a:b:bs
  else
    b:(simpleMergeB a bs)

sweepDownB :: [Block] -> [Block]
sweepDownB [] = []
sweepDownB (a : []) = a : []
sweepDownB (a:b:[]) =
  let(s,e) = twoSumB a b in
    [s,e]
sweepDownB (a : b : bs) =
  let (s,e) = twoSumB a b in
    s:(sweepDownB (simpleMergeB e bs))

zeroOverlapBRec :: [Block] -> [Block]
zeroOverlapBRec [] = []
zeroOverlapBRec (a : []) = a : []
zeroOverlapBRec (a : b : bs) =
  let (nb, na) = (twoSumB b a) in
    na : zeroOverlapBRec(nb:bs)

changeSignTo :: Block -> Sign -> Block
changeSignTo (ZeroBlock s e) newSign = (ZeroBlock s e)
changeSignTo (Block size exp oldSign list) newSign =
  Block size exp newSign list

changeExpTo :: Block -> Integer -> Block
changeExpTo (ZeroBlock s e) newExp =
  (ZeroBlock s newExp)
changeExpTo (Block size oldExp sign list) newExp =
  Block size newExp sign list

twoMultB :: Block -> Block -> (Block,Block)
twoMultB (ZeroBlock s e) y =
  (ZeroBlock s (e + (getExpB y)), ZeroBlock s (e + (getExpB y) - s))
twoMultB x (ZeroBlock s e) =
  (ZeroBlock s (e + (getExpB x)), ZeroBlock s (e + (getExpB x) - s))
twoMultB x y =
  getTwoBlocksFromList (twoMultL x y)

getTwoBlocksFromList :: [Block] -> (Block,Block)
getTwoBlocksFromList (x:[]) =
  (x, (ZeroBlock (getSizeOfBlock x) ((getExpB x) - (getSizeOfBlock x))))
getTwoBlocksFromList (x:y:[]) =
  (x,y)

twoMultL :: Block -> Block -> [Block]
twoMultL (ZeroBlock s e) y = [(ZeroBlock s e)]
twoMultL x (ZeroBlock s e) = [(ZeroBlock s e)]
twoMultL (Block size1 exp1 sign1 list1) (Block size2 exp2 sign2 list2) =
  zeroOverlapB
  (newExps
   (newSigns
    (twoMultHelper
     (Block size1 exp1 sign1 list1)
     (Block size2 exp2 sign2 list2)
    )
    (getNewSign sign1 sign2)
   )
   (exp1 + exp2)
  )

getNewSign :: Sign -> Sign -> Sign
getNewSign Plus Plus = Plus
getNewSign Minus Plus = Minus
getNewSign Plus Minus = Minus
getNewSign Minus Minus = Plus

newExps :: [Block] -> Integer -> [Block]
newExps [] i = []
newExps ((ZeroBlock _ _):y) i = newExps y i
newExps ((Block size exp sign list):y) i =
  (changeExpTo (Block size exp sign list) (exp+i)) : newExps y i

newSigns :: [Block] -> Sign -> [Block]
newSigns [] s = []
newSigns ((ZeroBlock _ _):y) s = newSigns y s
newSigns (x:y) s = (changeSignTo x s):(newSigns y s)


twoMultHelper :: Block -> Block -> [Block]
twoMultHelper (Block size1 exp1 sign1 list1) (Block size2 exp2 sign2 list2) =
  zeroOverlapB
  (reverse
   (boolMultRec
    (digitToBool list1)
    (reverse
     (digitToBool list2)
    )
    (1-size1)
    size1)
  )

boolMultRec ::
  [Bool] -> [Bool] -> Integer -> Integer -> [Block]
boolMultRec x [] n s = []
boolMultRec x (False : y) n s =
  boolMultRec x y (n+1) s
boolMultRec x (True : y) n s =
  (Block s n Plus (boolToDigit x)):(boolMultRec x y (n+1) s)


fma :: Block -> Block -> Block -> Block
fma a b c = 
  let muls = twoMultL a b in
  let (fs) = zeroOverlapB (c:muls) in
  if(fs == []) then (ZeroBlock (getSizeOfBlock a) (getExpB a))
  else
  (head fs)
  
blockDiv :: Block -> Block -> Block
blockDiv _ (ZeroBlock s e) = error "block divide by zero"
blockDiv (ZeroBlock s e) b = (ZeroBlock s e)
blockDiv (Block s1 e1 sn1 l1) (Block s2 e2 sn2 l2) = 
  let(nl,shift) = sigDiv (fromIntegral s1) l1 l2 in
  if(nl == []) then
    (ZeroBlock s1 e1)
  else
    (Block s1 (e1 - e2 + (toInteger shift)) (getNewSign sn1 sn2) nl)


sigDiv :: Int -> [Digit] -> [Digit] -> ([Digit],Int)
sigDiv s as bs =
  getDigitListFromDiv (boolDiv (digitToBool as) (digitToBool bs)) s 1

getDigitListFromDiv :: [Bool] -> Int -> Int -> ([Digit],Int)
getDigitListFromDiv (False:bs) i c =
  if(c > i + 2) then
    ([],0)
  else
    getDigitListFromDiv bs i (c+1)
getDigitListFromDiv (True:bs) i c =
  ((boolToDigit (take i (True:bs))),(i-c))

boolDiv :: [Bool] -> [Bool] -> [Bool]
boolDiv as bs = boolDivRec as bs []

boolDivRec :: [Bool] -> [Bool] ->[Bool]-> [Bool]
boolDivRec [] bs rs = 
  let nrs = rs ++ [False] in
  if(boolGreaterOrEqual nrs bs) then
    True:(boolDivRec [] bs (boolSubt nrs bs))
  else
    False:(boolDivRec [] bs nrs)
boolDivRec (a:as) bs rs = 
  let nrs = rs ++ [a] in
  if(boolGreaterOrEqual nrs bs) then
    True:(boolDivRec as bs (boolSubt nrs bs))
  else
    False:(boolDivRec as bs nrs)
       
listSize :: [Bool] -> Integer
listSize [] = 0
listSize (a:as) = 1 + (listSize as)
        
boolGreaterOrEqual :: [Bool] -> [Bool] -> Bool
boolGreaterOrEqual a b = 
  let sa = listSize a in
   let sb = listSize b in 
    if(sa > sb) then
      boolGreaterOrEqualRec a (padBackHelper(sa-sb) ++ b)
    else
      boolGreaterOrEqualRec (padBackHelper(sb-sa)++ a) b 

boolGreaterOrEqualRec :: [Bool] -> [Bool] -> Bool
boolGreaterOrEqualRec [] (b:bs) = False
boolGreaterOrEqualRec [] [] = True
boolGreaterOrEqualRec (a:as) [] = True
boolGreaterOrEqualRec (True:as) (False:bs) = True
boolGreaterOrEqualRec (True:as) (True:bs) = boolGreaterOrEqualRec as bs
boolGreaterOrEqualRec (False:as) (True:bs) = False
boolGreaterOrEqualRec (False:as) (False:bs) = boolGreaterOrEqualRec as bs


twoDivB :: Block -> Block -> (Block,Block)
twoDivB _ (ZeroBlock s e) = error "divide by zero"
twoDivB (ZeroBlock s e) b = ((ZeroBlock s (e-1)),(ZeroBlock s (e-s-1)))
twoDivB a b = 
  let z = blockDiv a b in
  let r = (blockToRational a) - (blockToRational z) * (blockToRational b) in
  if(r == 0%1) then
    (z,(ZeroBlock (getSizeOfBlock z) ((getExpB z) - (getSizeOfBlock z))))
  else
    let k = (rationalToBlock r (getSizeOfBlock a)) in
      (z,k)
      

getSFromBools :: Integer -> Integer -> [Bool] -> ([Digit],Integer)
getSFromBools 0 s bs = ([],(getSize bs) + s)
getSFromBools i s [] =
  let(nbs,ni) = (getSFromBools (i-1) (s+1) []) in
    ((Z:nbs),ni)
getSFromBools i s (True:bs) =
  let(nbs,ni) = (getSFromBools (i-1) (s+1) bs) in
    ((X:nbs),ni)
getSFromBools i s (False:bs) =
  let(nbs,ni) = ((getSFromBools (i-1) (s+1) bs)) in
    ((Z:nbs),ni)


rationalToBlock :: Rational -> Integer -> Block
rationalToBlock r s = 
  let(shiftUp,nr) = shiftRat pr 0 in
  let(bs) = reverse (intToBools (numerator nr)) in
  let (ds,shiftDown) = getSFromBools s 0 bs in
  (Block s ((getSize bs) - 1 - shiftUp) (sign) ds) 
  where sign = (if (r < 0) then Minus else Plus)
        pr = (if (r < 0) then -r else r)
  
  
intToBools :: Integer -> [Bool]
intToBools 0 = []
intToBools i = ((mod i 2) == 1):(intToBools (div i 2))

shiftRat :: Rational -> Integer -> (Integer,Rational)
shiftRat (r) i =
  if((denominator r) == 1) then (i,r)
  else if(mod (denominator r) 2 == 1) then error "Rat error"
       else shiftRat (r * 2) (i+1)


containsZero :: Block -> Bool
containsZero (ZeroBlock _ _) = True
containsZero (Block _ _ _ bs) = digitContainZero bs

digitContainZero :: [Digit] -> Bool
digitContainZero [] = False
digitContainZero (X:ds) = digitContainZero ds
digitContainZero (Z:ds) = True

getExpB :: Block -> Integer
getExpB (ZeroBlock _ e) = e
getExpB (Block _ e _ _) = e

getSizeOfBlock :: Block -> Integer
getSizeOfBlock  (ZeroBlock s _) = s
getSizeOfBlock  (Block s _ _ _) = s

overlap :: Block -> Block -> Bool
overlap b1 b2 =
  let(nb1,nb2) = twoSumB b1 b2 in
    if(expGreaterB b1 b2) then
      not(b1 == nb1)
    else
      not(b2 == nb1)



getBit :: Integer -> Block -> Block
getBit n (ZeroBlock s e) = (ZeroBlock s e)
getBit n (Block sz exp sn l) =
  if(checkBit sz l) then
    (Block sz (exp - sz + n) sn (X:(getSingleList (sz -1))))
  else
    (ZeroBlock sz exp)


checkBit :: Integer -> [Digit] -> Bool
checkBit 2 (X:bs) = True
checkBit 2 (Z:bs) = False
checkBit n (b:bs) = checkBit (n-1) bs
  
    
         


getZs :: Integer -> [Digit]
getZs 0 = []
getZs n = Z:(getZs (n-1))
         
         
twoSumWithBPB :: Block -> Block -> (Block,Block)
twoSumWithBPB a b =     
  let (s,e) = twoSumB a b in
   if(expGreaterByB s e ((getSizeOfBlock s) + 1)) then 
       (s,e) 
   else
     if(e == (ZeroBlock 0 1)) then 
         (s,e) 
     else
       if(isTie e) then 
           (s,e)  
       else
         let (Block size exp sign list) = e in
         let neg2 = (Block size (exp+1) (opp sign) (X:(getZs (size-1)))) in
         let (s2,e2) = twoSumB neg2 e in
         let neg1 = (Block size (exp+1) sign (X:(getZs (size-1)))) in
         let (s3,e3) = twoSumB s neg1 in
           (s3,s2)
          
           
isTie :: Block -> Bool
isTie (Block _ _ _ (X:zs)) = allZs zs

--Create Binary Streams for numbers between 0 and 1
ratToBS :: Rational -> [Bool]
ratToBS r = ratToBSHelper r 1

ratToBSHelper :: Rational -> Integer -> [Bool]
ratToBSHelper r n =
  if (r > 1 % (2^n)) then
    (True : (ratToBSHelper (r - (1%(2^n))) (n+1)))
  else
    if(r < 1 % (2^n)) then
      (False : (ratToBSHelper r (n+1)))
    else
      (True:[])

--Create BCL for rational numbers between -1 and 1 with size given
ratToBCL :: Rational -> Integer -> [Block]
ratToBCL r size =
  if(r > 0) then
    bsToBCL (ratToBS r) Plus (-1) size
  else
    if (r < 0) then
      bsToBCL (ratToBS (-r)) Minus (-1) size
    else
      []


bsToBCL :: [Bool] -> Sign -> Integer -> Integer -> [Block]
bsToBCL [] sign exp size = []
bsToBCL (False : bs) sign exp size =
  bsToBCL bs sign (exp-1) size
bsToBCL bs sign exp size =
  let (b,nexp, nbs) = getBlock bs sign exp size  in
    b:(bsToBCL nbs sign nexp size) 

getBlock ::
  [Bool] -> Sign -> Integer -> Integer -> (Block, Integer, [Bool])
getBlock bs sign exp size =
  let (nbs, nexp, nnbs) = getBools bs size exp in
    ((Block size exp sign (boolToDigit nbs)), nexp, nnbs)

getBools ::
  [Bool] -> Integer -> Integer -> ([Bool], Integer , [Bool])
getBools [] n exp =
  ((getFalses n), exp, [])
getBools bs 0 exp =
  ([],exp,bs)
getBools (True : bs) n exp  =
  let (nbs,nexp,nnbs) = getBools bs  (n-1)  (exp-1) in
    ((True:nbs),nexp,nnbs)
getBools (False : bs) n exp  =
  let (nbs,nexp,nnbs) = getBools bs  (n-1)  (exp-1) in
    ((False:nbs),nexp,nnbs)

xS = X : xS

shiftDownB :: [Block] -> ([Block],Integer)
shiftDownB ((ZeroBlock s e):as) = 
  if(e > 0) then
    let shift = (e + 1) in
    (((ZeroBlock s (-1)):(shiftDownRec as shift)),shift)
  else (((ZeroBlock s e):as),0)
shiftDownB ((Block s e sn l):as) = 
  if(e > 0) then 
    let shift = (e + 1) in
    (((Block s (-1) sn l):(shiftDownRec as shift)),shift)
  else (((Block s e sn l):as),0)
       
       
singleBitB  :: Block -> Bool
singleBitB (ZeroBlock _ _ ) = False
singleBitB (Block s e sn l) = singleDigit l

singleDigit (h:t) = allZs t
       
       
shiftDownRec :: [Block] -> Integer -> [Block]
shiftDownRec [] _ = []
shiftDownRec ((ZeroBlock s e):as) i =
  (ZeroBlock s (e-i)):(shiftDownRec as i)
shiftDownRec ((Block s e sn l):as) i =
  (Block s (e-i) sn l):(shiftDownRec as i)

shiftUpB :: Integer -> [Block] -> [Block]
shiftUpB i as = shiftDownRec as (-i)


hasZeroB :: Block -> Bool
hasZeroB (ZeroBlock _ _) = True
hasZeroB (Block _ _ _ l) = hasZD l 

hasZD :: [Digit] -> Bool
hasZD (X:rest) =  hasZ rest

integerLength :: [a] -> Integer
integerLength [] = 0
integerLength (_:rest) = 1 + integerLength rest


intToBCL :: Integer -> Integer -> [Block]
intToBCL i s =
  let l = (reverse (intToBools i)) in
    bsToBCL l Plus ((integerLength l) - 1) s


