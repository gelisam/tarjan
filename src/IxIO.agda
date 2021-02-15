{-# OPTIONS --no-termination --type-in-type #-}
module IxIO where

open import Data.Unit
  using (⊤; tt)

open import Graph
open import Int
open import MonadClasses
open import SimpleIO


module _ {I : Set} where
  data IxIO (@erased i : I) (A : Set) (@erased mkJ : A → I) : Set where
    UnsafeIxIO : IO A → IxIO i A mkJ

  runIxIO : ∀ {A} {@erased i mkJ} → IxIO i A mkJ → IO A
  runIxIO (UnsafeIxIO ioA) = ioA

  lift : ∀ {A} {@erased i}
       → IO A → IxIO i A (λ _ → i)
  lift ioA = UnsafeIxIO ioA

  IxIO-return : ∀ {A} {@erased i}
              → A → IxIO i A (λ _ → i)
  IxIO-return a = lift do
    return a
    where
      open Monad IO-Monad

  IxIO->>= : ∀ {A B} {@erased i mkJ mkK}
           → IxIO i A mkJ
           → ((a : A) → IxIO (mkJ a) B mkK)
           → IxIO i B mkK
  IxIO->>= (UnsafeIxIO ioA) f = UnsafeIxIO do
    a ← ioA
    runIxIO (f a)
    where
      open Monad IO-Monad

  instance
    IxIO-Monad : IxMonad IxIO
    IxIO-Monad = record
      { return = IxIO-return
      ; _>>=_  = IxIO->>=
      }
