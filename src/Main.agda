module Main where

open import Data.Fin using (#_)
open import Data.List using ([]; _∷_; map; upTo)
open import Data.Vec using (toList)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Bits

test : map (toList ∘ bits) (upTo 10)
     ≡                   (# 0 ∷ [])
     ∷                   (# 1 ∷ [])
     ∷             (# 1 ∷ # 0 ∷ [])
     ∷             (# 1 ∷ # 1 ∷ [])
     ∷       (# 1 ∷ # 0 ∷ # 0 ∷ [])
     ∷       (# 1 ∷ # 0 ∷ # 1 ∷ [])
     ∷       (# 1 ∷ # 1 ∷ # 0 ∷ [])
     ∷       (# 1 ∷ # 1 ∷ # 1 ∷ [])
     ∷ (# 1 ∷ # 0 ∷ # 0 ∷ # 0 ∷ [])
     ∷ (# 1 ∷ # 0 ∷ # 0 ∷ # 1 ∷ [])
     ∷ []
test = refl
