{-# OPTIONS --no-termination --type-in-type #-}
module Monad where

open import Data.Empty
  using (⊥)
open import Data.Unit
  using (⊤)


module _ {I : Set} where
  record IxMonad (M : (@erased p q : I → Set) → Set → Set) : Set where
    field
      return : ∀ {@erased p} {A}
             → A → M p p A
      _>>=_  : ∀ {@erased p q r} {A B}
             → M p q A
             → (A → M q r B)
             → M p r B

    _>>_ : ∀ {@erased p q r} {A}
         → M p q ⊤
         → M q r A
         → M p r A
    m⊤ >> mA = m⊤ >>= λ _ → mA

open IxMonad {{...}} public


Monad : (Set → Set) → Set
Monad M = IxMonad {I = ⊥} (λ _ _ → M)
