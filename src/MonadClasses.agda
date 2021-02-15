{-# OPTIONS --no-termination --type-in-type #-}
module MonadClasses where

open import Data.Unit
  using (⊤; tt)


record Monad (M : Set → Set) : Set where
  field
    return : ∀ {A} → A → M A
    _>>=_  : ∀  {A B} → M A → (A → M B) → M B

  _>>_ : ∀ {A} → M ⊤ → M A → M A
  m⊤ >> mA = m⊤ >>= λ _ → mA

module _ {I : Set} where
  record IxMonad (M : (@erased p : I → Set) → (A : Set) → (@erased q : A → I → Set) → Set) : Set where
    field
      return : ∀ {@erased p} {A}
             → A → M p A (λ _ → p)
      _>>=_  : ∀ {A B} {@erased p q r}
             → M p A q
             → ((a : A) → M (q a) B r)
             → M p B r

    _>>_ : ∀ {A} {@erased p q r}
         → M p ⊤ q
         → M (q tt) A r
         → M p A r
    m⊤ >> mA = m⊤ >>= λ _ → mA
