{-# OPTIONS --no-termination --type-in-type #-}
module Array where

open import Data.Unit
  using (⊤)

open import Int
open import SimpleIO


postulate
  Array         : Set → Set
  newArray      : ∀ {@erased A} → Int → A → IO (Array A)
  size          : ∀ {@erased A} → Array A → Int
  _[_]          : ∀ {@erased A} → Array A → Int → IO A
  _[_]≔_        : ∀ {@erased A} → Array A → Int → A → IO ⊤
  printIntArray : Array Int → IO ⊤
{-# FOREIGN GHC import Data.Ix #-}
{-# FOREIGN GHC import GHC.IOArray #-}
{-# COMPILE GHC Array    = type IOArray Int #-}
{-# COMPILE GHC newArray = \_ n -> newIOArray (0, n-1) #-}
{-# COMPILE GHC size     = \_ a -> rangeSize (boundsIOArray a) #-}
{-# COMPILE GHC _[_]     = \_ -> unsafeReadIOArray #-}
{-# COMPILE GHC _[_]≔_   = \_ -> unsafeWriteIOArray #-}
{-# FOREIGN GHC
  printArray :: Show a => IOArray Int a -> IO ()
  printArray a = do
    let indices = range (boundsIOArray a)
    xs <- mapM (unsafeReadIOArray a) indices
    print xs
#-}
{-# COMPILE GHC printIntArray = printArray #-}
