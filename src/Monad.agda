{-# OPTIONS --no-termination --type-in-type #-}
module Monad where

open import Data.Unit
  using (⊤)


module _ {I : Set} where
  record IxMonad (M : (@erased i j : I) → Set → Set) : Set where
    field
      return : ∀ {@erased i} {A}
             → A → M i i A
      _>>=_  : ∀ {@erased i j k} {A B}
             → M i j A
             → (A → M j k B)
             → M i k B

    _>>_ : ∀ {@erased i j k} {A}
         → M i j ⊤
         → M j k A
         → M i k A
    m⊤ >> mA = m⊤ >>= λ _ → mA

open IxMonad {{...}} public


Monad : (Set → Set) → Set
Monad M = IxMonad {I = ⊤} (λ _ _ → M)
