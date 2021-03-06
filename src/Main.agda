{-# OPTIONS --no-termination --type-in-type #-}
module Main where

open import Data.Empty
  using (⊥; ⊥-elim)
open import Data.Product
  using (_×_; _,_)
open import Data.Sum
  using (_⊎_; inj₁; inj₂)
open import Data.Unit
  using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; subst)

open import Array
open import Bool
open import Graph
open import IORef
open import Int
open import IxIO
open import MonadClasses
open import SimpleIO


NonEmpty : List Int → Set
NonEmpty []      = ⊥
NonEmpty (_ ∷ _) = ⊤

data _SubsequenceOf_ : List Int → List Int → Set where
  []     : [] SubsequenceOf []
  keep∷_ : ∀ {v xs ys}
         → xs SubsequenceOf ys
         → (v ∷ xs) SubsequenceOf (v ∷ ys)
  skip∷_ : ∀ {x xs ys}
         → xs SubsequenceOf ys
         → (x ∷ xs) SubsequenceOf ys

tail-of-subsequence : ∀ {xs y ys}
                    → xs SubsequenceOf (y ∷ ys)
                    → xs SubsequenceOf ys
tail-of-subsequence (keep∷ ss) = skip∷ ss
tail-of-subsequence (skip∷ ss) = skip∷ (tail-of-subsequence ss)

module _ (g : Graph)
         where
  n : Int
  n = size g

  -- 'withStack', 'push', and 'pop' are the thrusted base: their
  -- types describe the properties which we expect 'push' and 'pop'
  -- to obey, but we do not prove those properties. We cannot,
  -- because they use the FFI.

  withStack : {A : Set} {P : A → List Int → Set}
            → (Array Int → IORef Int → IxIO (λ xs → [] ≡ xs) A P)
            → IO A
  withStack body = do
    stack ← newArray n (fromℕ 0)
    stack-size ← newIORef (fromℕ 0)
    unsafeRunIxIO (body stack stack-size)
    where
      open Monad IO-Monad
  
  module _ (stack : Array Int)
           (stack-size : IORef Int)
           where
    push : (x : Int)
         → (@erased P Q : List Int → Set)
         → (@erased P→Q : ∀ xs → P xs → Q (x ∷ xs))
         → IxIO P ⊤ (λ _ → Q)
    push x _ _ _ = unsafeIxIO do
      i ← readIORef stack-size
      stack [ i ]≔ x
      modifyIORef stack-size succ
      where
        open Monad IO-Monad

    pop : (@erased P : List Int → Set)
        → (@erased Q : Int → List Int → Set)
        → (@erased P→NonEmpty : ∀ xs → P xs → NonEmpty xs)
        → (@erased P→Q : ∀ x xs → P (x ∷ xs) → Q x xs)
        → IxIO P Int Q
    pop _ _ _ _ = unsafeIxIO do
      modifyIORef stack-size pred
      i ← readIORef stack-size
      stack [ i ]
      where
        open Monad IO-Monad

    -- From now on, we no longer use unsafe functions, and we never
    -- interact with 'stack' nor 'stack-size' directly, we always
    -- go through 'push' and 'pop'. The compiler would catch our
    -- mistake if we wrote a variant of the algorithm in which the
    -- stack was not guaranteed to be non-empty when we call 'pop'.
    --
    -- It would not catch cases in which e.g. we cheat by using
    -- postulates, by writing proofs which exploit --no-termination
    -- or --type-in-type, or by manipulating the stack directly;
    -- but the original challenge was for Haskell, which would ¬
    -- catch those either, so I chose not to make life
    -- unnecessarily hard for myself by using Agda's stricter
    -- default level of paranoia.
    --
    -- It also doesn't catch any other kind of mistake, such as
    -- buffer _over_ flows by pushing more than 'n' elements. The
    -- other arrays in the program are similarly unchecked, I am
    -- focusing solely on the problematic 'pop' call.
    -- 
    -- I recommend reading the rest of this file starting from the
    -- bottom, because Agda wants me to write the function
    -- definitions before the function calls, and that means that
    -- the end of the algorithm is at the top while the start of
    -- the algorithm is at the bottom. I have included the part of
    -- the Java code which each function transliterates, for easy
    -- reference.

    module _
           (marked : Array Bool)
           (id : Array Int)
           (low : Array Int)
           (pre : IORef Int)
           (count : IORef Int)
           where
      module M1 (dfs : ∀ {@erased vs}
                     → Int
                     → IxIO (λ xs → xs SubsequenceOf vs)
                            ⊤
                            (λ _ xs → xs SubsequenceOf vs))
                (min : IORef Int)
                (v : Int)
                {@erased vs : List Int}
                where
        @erased P : List Int → Set
        P xs = xs SubsequenceOf (v ∷ vs)

        @erased Q : Int → List Int → Set
        Q x xs = (x ≡ v × xs SubsequenceOf vs)
               ⊎ xs SubsequenceOf (v ∷ vs)

        @erased R : List Int → Set
        R xs = xs SubsequenceOf vs

        @erased P→NonEmpty : ∀ xs → P xs → NonEmpty xs
        P→NonEmpty _ (keep∷ _) = tt
        P→NonEmpty _ (skip∷ _) = tt

        @erased P→Q : ∀ x xs → P (x ∷ xs) → Q x xs
        P→Q _ _ (keep∷ ss) = inj₁ (refl , ss)
        P→Q _ _ (skip∷ ss) = inj₂ ss

        @erased Q→R : ∀ x xs → (x == v) ≡ true × Q x xs → R xs
        Q→R _ _ (prf , inj₁ (_ , i)) = i
        Q→R _ _ (prf , inj₂ i) = tail-of-subsequence i

        @erased Q→P : ∀ x xs → (x == v) ≡ false × Q x xs → P xs
        Q→P _ _ (prf , inj₂ i) = i
        Q→P x _ (prf , inj₁ (x≡v , _)) = ⊥-elim (x≢v x≡v)
          where
            x≢v : x ≢ v
            x≢v = subst (λ b → if b then x ≡ v else x ≢ v) prf (==→≡ x v)

        -- int w;
        -- do {
        --     w = stack.pop();
        --     id[w] = count;
        --     low[w] = G.V();
        -- } while (w != v);
        -- count++;
        dfsWhile : IxIO P ⊤ (λ _ → R)
        dfsWhile = do
          w ← pop P Q P→NonEmpty P→Q
          count-value ← lift (readIORef count)
          lift (id [ w ]≔ count-value)
          lift (low [ w ]≔ n)
          ixIf w == v
            then (do
              rearrange (Q→R w)
              lift (modifyIORef count succ))
            else (do
              rearrange (Q→P w)
              dfsWhile)
          where
            open IxMonad IxIO-Monad

        -- for (int w : G.adj(v)) {
        --     if (!marked[w]) dfs(G, w);
        --     if (low[w] < min) min = low[w];
        -- }
        -- if (min < low[v]) {
        --     low[v] = min;
        --     return;
        -- }
        -- do {...}
        dfsFor : List Node
               → IxIO P ⊤ (λ _ → R)
        dfsFor (w ∷ out-edges) = do
          w-marked? ← lift (marked [ w ])
          ixWhen (not w-marked?) (do
            rearrange (λ _ (_ , p) → p)
            dfs w)
          low[w] ← lift (low [ w ])
          min-value ← lift (readIORef min)
          lift (when (low[w] < min-value) (writeIORef min low[w]))
          dfsFor out-edges
          where
            open IxMonad IxIO-Monad
        dfsFor [] = do
          min-value ← lift (readIORef min)
          low[v] ← lift (low [ v ])
          if (min-value < low[v])
            then (do
              rearrange (λ _ i → tail-of-subsequence i)
              lift (low [ v ]≔ min-value))
            else dfsWhile
          where
            open IxMonad IxIO-Monad
      open M1 using (dfsWhile; dfsFor)

      module M2 (recur : ∀ {@erased vs}
                       → Int
                       → IxIO (λ xs → xs SubsequenceOf vs)
                              ⊤
                              (λ _ xs → xs SubsequenceOf vs))
                (v : Int)
                {@erased vs : List Int}
                where
        @erased P : List Int → Set
        P xs = xs SubsequenceOf vs

        @erased Q : List Int → Set
        Q xs = xs SubsequenceOf (v ∷ vs)

        @erased P→Q : ∀ xs → P xs → Q (v ∷ xs)
        P→Q _ ss = keep∷ ss

        -- marked[v] = true;
        -- low[v] = pre++;
        -- int min = low[v];
        -- stack.push(v);
        -- for (int w : G.adj(v)) {...}
        dfs : IxIO P ⊤ (λ _ → P)
        dfs = do
          lift (marked [ v ]≔ true)
          low[v] ← lift (readIORef pre)
          lift (low [ v ]≔ low[v])
          lift (modifyIORef pre succ)
          min ← lift (newIORef low[v])
          push v P Q P→Q
          out-edges ← lift (g [ v ])
          dfsFor recur min v out-edges
          where
            open IxMonad IxIO-Monad
      dfs : ∀ {@erased vs}
          → Int
          → IxIO (λ xs → xs SubsequenceOf vs)
                 ⊤
                 (λ _ xs → xs SubsequenceOf vs)
      dfs v = M2.dfs dfs v

      -- for (int v = 0; v < G.V(); v++) {
      --     if (!marked[v]) dfs(G, v);
      -- }
      tarjanFor : ∀ v {@erased vs}
                → IxIO (λ xs → xs SubsequenceOf vs)
                       ⊤
                       (λ _ xs → xs SubsequenceOf vs)
      tarjanFor v = do
        ixWhen (v < n) do
          rearrange (λ _ (_ , p) → p)
          v-marked? ← lift (marked [ v ])
          ixWhen (not v-marked?) do
            rearrange (λ _ (_ , p) → p)
            dfs v
          tarjanFor (succ v)
        where
          open IxMonad IxIO-Monad

  -- marked = new boolean[G.V()];
  -- stack = new Stack<Integer>();
  -- id = new int[G.V()]; 
  -- low = new int[G.V()];
  -- for (int v = 0; ...) {...}
  tarjan : IO (Array Int)
  tarjan = withStack λ stack stack-size → do
    marked ← lift (newArray n false)
    id ← lift (newArray n (fromℕ 0))
    low ← lift (newArray n (fromℕ 0))
    pre ← lift (newIORef (fromℕ 0))
    count ← lift (newIORef (fromℕ 0))
    rearrange (λ xs []≡xs → subst (λ xs → xs SubsequenceOf []) []≡xs [])
    tarjanFor stack stack-size marked id low pre count (fromℕ 0)
    return id
    where
      open IxMonad IxIO-Monad

main : IO ⊤
main = do
  g ← mkExampleGraph
  r ← tarjan g
  printIntArray r -- should be [0,0,0,2,2,1,1,3]
  return tt
  where
    open Monad IO-Monad
