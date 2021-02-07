{-# OPTIONS --no-termination --type-in-type #-}
module Monad where

open import Data.Unit
  using (⊤)


record Monad (M : Set → Set) : Set where
  field
    return : ∀ {A} → A → M A
    _>>=_  : ∀  {A B} → M A → (A → M B) → M B

  _>>_ : ∀ {A} → M ⊤ → M A → M A
  m⊤ >> mA = m⊤ >>= λ _ → mA

open Monad {{...}} public
