module Floating where

import FD
import Blocks

import Data.Ratio


newtype FDWrap = FDWrap FD deriving (Show,Read)

wrapFD :: FD -> FDWrap
wrapFD a = FDWrap a

unwrapFD :: FDWrap -> FD
unwrapFD (FDWrap a) = a

unwrapListFD :: [FDWrap] -> [FD]
unwrapListFD as = map unwrapFD as

wrapListFD :: [FD]-> [FDWrap]
wrapListFD as = map wrapFD as


class Floats a where
  fShow :: a -> String
  floatEq :: a -> a -> Bool
  floatCompare :: a -> a -> Ordering
  negFloatCompare :: a -> a -> Ordering
  toRat :: a -> Rational
  isZero :: a -> Bool
  twoSum :: a -> a -> (a,a)
  twoMult :: a -> a -> (a,a)
  twoDiv :: a -> a -> (a,a)
  negate :: a -> a
  getExp :: a -> Integer
  getSize :: a -> Integer
  dominate :: a -> a -> Bool
  overlap :: a -> a -> Bool
  expGreater :: a -> a -> Bool
  expGreaterBy :: Integer -> a -> a -> Bool
  twoSumRN :: a -> a -> (a,a)
  createZero :: Integer -> Integer -> a
  ratToFloat :: Rational -> Integer -> [a]
  shiftDown :: [a] -> ([a],Integer)
  shiftUp :: Integer -> [a] -> [a]
  domPOne :: a -> a -> Bool
  hasZ :: a -> Bool
  intToFloat :: Integer -> Integer -> [a]
  singleBit :: a -> Bool
  domPOne a b = (expGreaterBy ((Floating.getSize a) + 1) a b)
  overlap a b = ((not (dominate a b)) && (not (dominate b a)))
  floatEq a b = (toRat a) == (toRat b)
  dominate a b = let(s,e) = twoSumRN a b in (floatEq a s)
  oppSign :: a -> a -> Bool
  oppSign a b = (((toRat a) > 0) && ((toRat b) < 0)) || (((toRat b) > 0) && ((toRat a) < 0))
  floatCompare a b = if(expGreater a b) then GT
                     else if(expGreater b a) then LT
                          else EQ
  negFloatCompare a b = 
    case floatCompare a b of
      GT -> LT
      LT -> GT
      EQ -> EQ
  
                               
  

  
instance Floats FDWrap where
  fShow a = show a
  toRat a = fdToRat (unwrapFD a)
  isZero a = fdIsZero (unwrapFD a)
  twoSum a b = let(s,e) = (twoSumFD (unwrapFD a) (unwrapFD b)) in ((wrapFD s),(wrapFD e))
  twoMult a b = let(s,e) = (twoMultFD (unwrapFD a) (unwrapFD b)) in ((wrapFD s),(wrapFD e))
  twoDiv a b =  let(s,e) = (twoDivFD (unwrapFD a) (unwrapFD b)) in ((wrapFD s),(wrapFD e))
  getExp a = (getExpFD (unwrapFD a))
  getSize a = doubleSigSize
  expGreater a b = (expGreaterFD (unwrapFD a) (unwrapFD b))
  expGreaterBy i a b = (expGreaterByFD i (unwrapFD a) (unwrapFD b))
  negate a = wrapFD (negateFD (unwrapFD a))
  twoSumRN a b = let(s,e) = (twoSumFD (unwrapFD a) (unwrapFD b)) in ((wrapFD s),(wrapFD e))
  ratToFloat _ _ = [] --need to implement
  intToFloat i s = []
  shiftDown a = let(l,e) = shiftDownFD (unwrapListFD a) in ((wrapListFD l),e)
  shiftUp i a = wrapListFD (shiftUpFD i (unwrapListFD a))
  createZero _ e = wrapFD (createZeroFD e)
  hasZ b = True
  singleBit a = False
  
instance Floats Block where
  fShow a = (show a)
  toRat a = blockToRational a
  isZero a = isBlockZero a
  twoSum a b = twoSumB a b
  twoMult a b = twoMultB a b
  twoDiv a b = twoDivB a b
  negate a = negateBlock a
  getExp a = getExpB a
  getSize a = getSizeOfBlock a
  expGreater a b = expGreaterB a b
  expGreaterBy i a b = expGreaterByB a b i
  twoSumRN a b = twoSumWithBPB a b
  createZero s e = createZeroBlock s e
  ratToFloat r i = ratToBCL r i
  intToFloat i s = intToBCL i s 
  shiftDown a = shiftDownB a
  shiftUp i b = shiftUpB i b
  hasZ b = hasZeroB b
  singleBit = singleBitB
  

  
  
  
  

  
