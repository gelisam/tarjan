
module Main where

open import Data.Fin using (Fin)
open import Data.Nat using (ℕ ; zero; suc)
open import Data.Nat.DivMod using (_div_; _mod_)
open import Data.List using (List; []; _∷ʳ_)

Bit : Set
Bit = Fin 2

bits : ℕ → List Bit
bits 0 = []
bits n = bits (n div 2) ∷ʳ n mod 2
