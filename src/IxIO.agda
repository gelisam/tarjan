{-# OPTIONS --no-termination --type-in-type #-}
module IxIO where

open import Data.Unit
  using (⊤; tt)

open import Graph
open import Int
open import MonadClasses
open import SimpleIO


module _ {I : Set} where
  data IxIO (@erased P : I → Set)
            (A : Set)
            (@erased Q : A → I → Set)
          : Set where
    unsafeIxIO : IO A
               → IxIO P A Q

  unsafeRunIxIO : ∀ {A} {@erased P Q}
                → IxIO P A Q
                → IO A
  unsafeRunIxIO (unsafeIxIO ioA) = ioA

  lift : ∀ {A} {@erased P}
       → IO A
       → IxIO P A (λ _ → P)
  lift ioA = unsafeIxIO ioA

  IxIO-return : ∀ {A} {@erased P}
              → A
              → IxIO P A (λ _ → P)
  IxIO-return a = lift do
    return a
    where
      open Monad IO-Monad

  IxIO->>= : ∀ {A B} {@erased P Q R}
           → IxIO P A Q
           → ((a : A) → IxIO (Q a) B R)
           → IxIO P B R
  IxIO->>= (unsafeIxIO ioA) f = unsafeIxIO do
    a ← ioA
    unsafeRunIxIO (f a)
    where
      open Monad IO-Monad

  instance
    IxIO-Monad : IxMonad IxIO
    IxIO-Monad = record
      { return = IxIO-return
      ; _>>=_  = IxIO->>=
      }

  rearrange : {@erased P Q : I → Set}
            → (@erased P→Q : ∀ i → P i → Q i)
            → IxIO P ⊤ (λ _ → Q)
  rearrange P→Q = unsafeIxIO do
    return tt
    where
      open Monad IO-Monad
