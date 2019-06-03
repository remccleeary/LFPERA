module FD where

import Data.List
import Data.Ratio
import Data.Tuple

--Needed for FMA (modified from altfloat package by Nick Bowler)
import Foreign
import Foreign.C

import Unsafe.Coerce

import Test.QuickCheck


type FD = (Integer,Double) 

type FF = (Integer,Float)

testOn :: Bool
testOn = False


--FMA is not natively supported in Haskell so we need to make
--a call to c's fma
foreign import ccall unsafe "fma"
    c_fma :: CDouble -> CDouble -> CDouble -> CDouble
             
toDouble :: CDouble -> Double
toDouble a = if(isIEEE a) then unsafeCoerce a else error "Not IEEE"
--Direct binary conversion, both are IEEE standard


toCDouble :: Double -> CDouble
toCDouble a = if(isIEEE a) then unsafeCoerce a else error "Not IEEE"
--Direct binary conversion. 
             
fma :: Double -> Double -> Double -> Double
fma a b c = toDouble(c_fma (toCDouble a) (toCDouble b) (toCDouble c))
--End FMA

expInt :: Integer -> Integer -> Integer
expInt a 0 = 1
expInt a e = a * (expInt a (e-1))

fdToRat :: FD -> Rational
fdToRat (i,d) =
  if (i > 0) then
    (toRational d) * ((expInt 2 i)%1)
  else
    (toRational d) / ((expInt 2 (-i))%1)

fdEq :: FD -> FD -> Bool
fdEq a b = (fdToRat a) == (fdToRat b)

doubleSigSize :: Integer
doubleSigSize = 53
  
dominateFD :: FD -> FD -> Bool
dominateFD (i1,_) (i2,_) = i1 > i2 + doubleSigSize

getExpFD :: FD -> Integer
getExpFD (i,d) = i

getDouble :: FD -> Double
getDouble (i,d) = d

expGreaterFD :: FD -> FD -> Bool
expGreaterFD (i1,_) (i2,_) = i1 > i2

expGreaterByFD :: Integer -> FD -> FD -> Bool
expGreaterByFD e (i1,_) (i2,_)  = i1 >= i2 + e

twoSumDouble :: Double -> Double -> (Double,Double)
twoSumDouble a 0.0 = (a,0.0)
twoSumDouble 0.0 b = (b,0.0)
twoSumDouble a b = 
  if(abs(b) > abs(a)) then twoSumDouble b a
  else
  let s = a + b in
  let z = s - a in
  let t = b - z in
  (s,t)
                       
getExpDif :: FD -> FD -> Integer
getExpDif (i1,_) (i2,_) = i1 - i2


overlap :: FD -> FD -> Bool
overlap a b = abs(getExpDif a b) < doubleSigSize

doubleToFD :: Double -> FD
doubleToFD d = 
  let e = exponent d in
  let d' = scaleFloat (-e) d in
  (fromIntegral e,d')
  

fdIsZero :: FD -> Bool
fdIsZero (i,d1) = (d1 == 0.0)

shiftAndNormalizeFDS :: Integer -> Double -> Double -> (FD,FD)
shiftAndNormalizeFDS i d1 d2 = 
  if(d2 == 0.0) then
    let (shiftI1) = (exponent d1) in
    let nd1 = scaleFloat (-shiftI1) d1 in
    ((i + (fromIntegral shiftI1),nd1),(i - doubleSigSize,0.0))
  else
    let (shiftI1) = exponent d1 in
    let (shiftI2) = exponent d2 in
    let nd1 = scaleFloat (-shiftI1) d1 in
    let nd2 = scaleFloat (-shiftI2) d2 in
                         ((i + (fromIntegral shiftI1),nd1),((i  + (fromIntegral shiftI2)),nd2))
                         
shiftAndNormalizeFD :: Integer -> Double -> FD
shiftAndNormalizeFD i d = 
  if(d == 0.0) then (i,d)
  else 
    let(shift) = exponent d in
    let nd = scaleFloat (-shift) d in
    ((i + (fromIntegral shift)),nd)


negateFD :: FD -> FD
negateFD (i,d) = (i,-d)

createZeroFD ::Integer -> FD
createZeroFD e = (e,0.0)

twoSumFD :: FD -> FD -> (FD, FD)
twoSumFD a b =
  if(b > a) then twoSumFD b a 
  else if(dominateFD a b) then 
         (a,b)
       else
         let expDif = getExpDif a b in
         let (i1,d1) = a in
         let (i2,d2) = b in
         let d2' = scaleFloat (fromInteger(-expDif)) d2 in 
         let (d1',d2'') = twoSumDouble d1 d2' in 
         let (s,e) = shiftAndNormalizeFDS i1 d1' d2'' in 
         let e' =
               (if((getDouble e) == 0.0) then 
                  (((getExpFD s) - doubleSigSize),0.0)
                else e)
         in (s,e')
                         
                                                     
twoMultDouble :: Double -> Double -> (Double,Double)
twoMultDouble a b = 
  let r1 = a * b in
  let r2 = fma a b (-r1) in
  (r1,r2) 

  
twoMultFD :: FD -> FD -> (FD,FD)
twoMultFD (i1,d1) (i2,d2) = 
  let(d1',d2') = twoMultDouble d1 d2 in
  let exp = i1 + i2 in
  let s = shiftAndNormalizeFD exp d1' in
  let e = shiftAndNormalizeFD (exp) d2' in
  if(d2' == 0.0) then
    (s,(shiftAndNormalizeFD (exp - (doubleSigSize)) d2')) 
  else
    (s,e) 
  
    
twoDivDouble :: Double -> Double -> (Double,Double)
twoDivDouble a b = 
  let z = a / b in
  let k = fma z b (-a) in
    (z,-k)

twoDivFD :: FD -> FD -> (FD,FD)
twoDivFD (i1,d1) (i2,d2) =  
  let(d1',d2') = twoDivDouble d1 d2 in
  let exp1 = i1 - i2 in
  let s = shiftAndNormalizeFD exp1 d1' in
  let e = shiftAndNormalizeFD i1 d2' in
  if((getDouble e) == 0.0) then
    (s,(((getExpFD s) - doubleSigSize),0.0))
  else
   (s,e)
   
           
         
shiftDownFD :: [FD] -> ([FD],Integer)
shiftDownFD ((e,0.0):as) = 
  if(e > 0) then
    let shift = (e + 1) in
    (((-1),0.0):(shiftDownFDRec as shift),shift)
  else (((e,0.0):as),0)
shiftDownFD ((e,d):as) = 
  if(e > 0) then 
    let shift = (e + 1) in
    ((((-1),d):(shiftDownFDRec as shift)),shift)
  else (((e,d):as),0)

shiftDownFDRec :: [FD] -> Integer -> [FD]
shiftDownFDRec ((e,0.0):as) i = ((e-i),0.0):(shiftDownFDRec as i)
shiftDownFDRec ((e,d):as) i = ((e-i),d):(shiftDownFDRec as i)

shiftUpFD :: Integer -> [FD] -> [FD]
shiftUpFD i as = shiftDownFDRec as (-i)
  
  

twoFDDiv :: FD -> FD -> [FD]
twoFDDiv a b = 
  if((getDouble a) == 0.0) then
    [(((getExpFD a) - doubleSigSize),0.0)] 
  else
    let(s,e) = twoDivFD a b in
      s:(twoFDDiv e b)

