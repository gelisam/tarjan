{-# OPTIONS --no-termination-check #-}
module Main where

open import Data.Fin using (Fin)
open import Data.Nat using (ℕ ; zero; suc)
open import Data.Nat.DivMod using (_div_; _mod_)
open import Data.Vec using (Vec; []; _∷ʳ_)

Bit : Set
Bit = Fin 2

log2 : ℕ → ℕ
log2 0 = 0
log2 n = suc (log2 (n div 2))

bits : (n : ℕ) → Vec Bit (log2 n)
bits 0 = []
bits n = bits (n div 2) ∷ʳ n mod 2
