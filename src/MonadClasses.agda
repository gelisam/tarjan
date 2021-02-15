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
  record IxMonad (M : (@erased i : I) → (A : Set) → (@erased mkJ : A → I) → Set) : Set where
    field
      return : ∀ {@erased i} {A}
             → A → M i A (λ _ → i)
      _>>=_  : ∀ {A B} {@erased i mkJ mkK}
             → M i A mkJ
             → ((a : A) → M (mkJ a) B mkK)
             → M i B mkK

    _>>_ : ∀ {A} {@erased i mkJ mkK}
         → M i ⊤ mkJ
         → M (mkJ tt) A mkK
         → M i A mkK
    m⊤ >> mA = m⊤ >>= λ _ → mA
