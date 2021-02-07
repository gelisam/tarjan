{-# OPTIONS --no-termination --type-in-type #-}
module IxIO where

open import Data.Unit
  using (⊤; tt)

open import Graph
open import Int
open import Monad
open import SimpleIO
  using (IO)


module _ {I : Set} where
  data IxIO (@erased i j : I) (A : Set) : Set where
    UnsafeIxIO : IO A → IxIO i j A

  runIxIO : ∀ {@erased i j} {A} → IxIO i j A → IO A
  runIxIO (UnsafeIxIO ioA) = ioA

  IxIO-return : ∀ {@erased i} {A}
              → A → IxIO i i A
  IxIO-return a = UnsafeIxIO do
    return a

  IxIO->>= : ∀ {@erased i j k} {A B}
           → IxIO i j A
           → (A → IxIO j k B)
           → IxIO i k B
  IxIO->>= (UnsafeIxIO ioA) f = UnsafeIxIO do
    a ← ioA
    runIxIO (f a)

  instance
    IxIO-Monad : IxMonad IxIO
    IxIO-Monad = record
      { return = IxIO-return
      ; _>>=_  = IxIO->>=
      }
