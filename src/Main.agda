
module Main where

open import Data.Fin using (Fin)
open import Data.Nat using (ℕ ; zero; suc)
open import Data.Nat.DivMod using (_div_; _mod_)
open import Data.Vec using (Vec; []; _∷ʳ_)

Bit : Set
Bit = Fin 2

log2 : ℕ → ℕ
log2 zero      = zero
log2 n@(suc _) = suc (log2 (n div 2))

bits : (n : ℕ) → Vec Bit (log2 n)
bits zero      = []
bits n@(suc _) = bits (n div 2) ∷ʳ n mod 2
