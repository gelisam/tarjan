module Main where

open import Data.Fin using (Fin)
open import Data.Nat using (ℕ ; zero; suc)
open import Data.Nat.DivMod using (_div_; _mod_)
open import Data.Vec using (Vec; []; _∷ʳ_)

Bit : Set
Bit = Fin 2

limitedLog2 : ℕ → ℕ → ℕ
limitedLog2 zero        _         = zero
limitedLog2 (suc limit) zero      = zero
limitedLog2 (suc limit) n@(suc _) = suc (limitedLog2 limit (n div 2))

log2 : ℕ → ℕ
log2 n = limitedLog2 n n

bits : (n : ℕ) → Vec Bit (log2 n)
bits zero      = []
bits n@(suc _) = bits (n div 2) ∷ʳ n mod 2
