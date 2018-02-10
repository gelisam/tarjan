module Main where

open import Data.Nat using (ℕ ; zero; suc)
open import Data.Nat.DivMod using (_div_)

limitedLog2 : ℕ → ℕ → ℕ
limitedLog2 zero        _         = zero
limitedLog2 (suc limit) zero      = zero
limitedLog2 (suc limit) n@(suc _) = suc (limitedLog2 limit (n div 2))

log2 : ℕ → ℕ
log2 n = limitedLog2 n n
