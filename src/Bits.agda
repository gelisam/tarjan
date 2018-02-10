module Bits where

open import Data.Fin using (Fin; #_)
open import Data.Nat using (ℕ ; zero; suc)
open import Data.Nat.DivMod using (_div_; _mod_)
open import Data.Vec using (Vec; []; _∷ʳ_; [_])

Bit : Set
Bit = Fin 2

limitedLog2 : ℕ → ℕ → ℕ
limitedLog2 zero        _         = zero
limitedLog2 (suc limit) zero      = zero
limitedLog2 (suc limit) n@(suc _) = suc (limitedLog2 limit (n div 2))

limitedBits : (limit : ℕ)
            → (n : ℕ)
            → Vec Bit (limitedLog2 limit n)
limitedBits zero        _         = []
limitedBits (suc limit) zero      = []
limitedBits (suc limit) n@(suc _) = limitedBits limit (n div 2) ∷ʳ n mod 2

log2 : ℕ → ℕ
log2 zero      = 1
log2 n@(suc _) = limitedLog2 n n

bits : (n : ℕ) → Vec Bit (log2 n)
bits zero      = [ # 0 ]
bits n@(suc _) = limitedBits n n
