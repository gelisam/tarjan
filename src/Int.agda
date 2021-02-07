{-# OPTIONS --no-termination --type-in-type #-}
module Int where

open import Agda.Builtin.Int
  renaming (Int to Integer)
open import Data.Bool
  using (Bool)
open import Data.Nat public
  using (ℕ)
open import Data.Unit
  using (⊤)
open import Foreign.Haskell.Coerce
  using (coerce)

open import SimpleIO


postulate
  Int         : Set
  succ        : Int → Int
  pred        : Int → Int
  _==_        : Int → Int → Bool
  _<_         : Int → Int → Bool
  fromInteger : Integer → Int
  printInt    : Int → IO ⊤
{-# COMPILE GHC Int         = type Int #-}
{-# COMPILE GHC succ        = succ #-}
{-# COMPILE GHC pred        = pred #-}
{-# COMPILE GHC _==_        = (==) #-}
{-# COMPILE GHC _<_         = (<) #-}
{-# COMPILE GHC fromInteger = fromInteger #-}
{-# COMPILE GHC printInt    = print #-}

fromℕ : ℕ → Int
fromℕ n = fromInteger (coerce n)
