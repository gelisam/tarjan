{-# OPTIONS --no-termination --type-in-type #-}
module MonadClasses where

open import Data.Unit
  using (⊤)


record Monad (M : Set → Set) : Set where
  field
    return : ∀ {A} → A → M A
    _>>=_  : ∀  {A B} → M A → (A → M B) → M B

  _>>_ : ∀ {A} → M ⊤ → M A → M A
  m⊤ >> mA = m⊤ >>= λ _ → mA

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
