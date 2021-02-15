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
open import Linked
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

  module _ (marked : Array Bool)
           (id : Array Int)
           (low : Array Int)
           (stack : Array Int)
           (stack-size : IORef Int)
           (pre : IORef Int)
           (count : IORef Int)
           where
    push : (x : Int)
         → (P Q : List Int → Set)
         → (∀ xs → P xs → Q (x ∷ xs))
         → IxIO P ⊤ (λ _ → Q)
    push x _ _ _ = unsafeIxIO do
      i ← readIORef stack-size
      stack [ i ]≔ x
      modifyIORef stack-size succ
      where
        open Monad IO-Monad

    pop : (P : List Int → Set)
        → (Q : Int → List Int → Set)
        → (∀ xs → P xs → NonEmpty xs)
        → (∀ x xs → P (x ∷ xs) → Q x xs)
        → IxIO P Int Q
    pop _ _ _ _ = unsafeIxIO do
      modifyIORef stack-size pred
      i ← readIORef stack-size
      stack [ i ]
      where
        open Monad IO-Monad

    module M1 (dfs : ∀ {vs}
                   → Int
                   → IxIO (λ xs → xs SubsequenceOf vs)
                          ⊤
                          (λ _ xs → xs SubsequenceOf vs))
              (min : IORef Int)
              (v : Int)
              {vs : List Int}
              where
      P : List Int → Set
      P xs = xs SubsequenceOf (v ∷ vs)

      Q : Int → List Int → Set
      Q x xs = (x ≡ v × xs SubsequenceOf vs)
             ⊎ xs SubsequenceOf (v ∷ vs)

      R : List Int → Set
      R xs = xs SubsequenceOf vs

      P→NonEmpty : ∀ xs → P xs → NonEmpty xs
      P→NonEmpty _ (keep∷ _) = tt
      P→NonEmpty _ (skip∷ _) = tt

      P→Q : ∀ x xs → P (x ∷ xs) → Q x xs
      P→Q _ _ (keep∷ ss) = inj₁ (refl , ss)
      P→Q _ _ (skip∷ ss) = inj₂ ss

      Q→R : ∀ x xs → (x == v) ≡ true × Q x xs → R xs
      Q→R _ _ (prf , inj₁ (_ , i)) = i
      Q→R _ _ (prf , inj₂ i) = tail-of-subsequence i

      Q→P : ∀ x xs → (x == v) ≡ false × Q x xs → P xs
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

    module M2 (recur : ∀ {vs}
                     → Int
                     → IxIO (λ xs → xs SubsequenceOf vs)
                            ⊤
                            (λ _ xs → xs SubsequenceOf vs))
              (v : Int)
              {vs : List Int}
              where
      P : List Int → Set
      P xs = xs SubsequenceOf vs

      Q : List Int → Set
      Q xs = xs SubsequenceOf (v ∷ vs)

      P→Q : ∀ xs → P xs → Q (v ∷ xs)
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
    dfs : ∀ {vs}
        → Int
        → IxIO (λ xs → xs SubsequenceOf vs)
               ⊤
               (λ _ xs → xs SubsequenceOf vs)
    dfs v = M2.dfs dfs v

--    -- for (int v = 0; v < G.V(); v++) {
--    --     if (!marked[v]) dfs(G, v);
--    -- }
--    tarjanFor : Int → IO ⊤
--    tarjanFor v = do
--      when (v < n) do
--        v-marked? ← marked [ v ]
--        when (not v-marked?) (runIxIO (dfs v))
--        tarjanFor (succ v)
--      where
--        open Monad IO-Monad
--
--  -- marked = new boolean[G.V()];
--  -- stack = new Stack<Integer>();
--  -- id = new int[G.V()]; 
--  -- low = new int[G.V()];
--  -- for (int v = 0; ...) {...}
--  tarjan : IO (Array Int)
--  tarjan = do
--    marked ← newArray n false
--    stack ← newArray n (fromℕ 0)
--    stack-size ← newIORef (fromℕ 0)
--    id ← newArray n (fromℕ 0)
--    low ← newArray n (fromℕ 0)
--    pre ← newIORef (fromℕ 0)
--    count ← newIORef (fromℕ 0)
--    tarjanFor marked id low stack stack-size pre count (fromℕ 0)
--    return id
--    where
--      open Monad IO-Monad
--
--main : IO ⊤
--main = do
--  g ← mkExampleGraph
--  r ← tarjan g
--  printIntArray r -- should be [0,0,0,2,2,1,1,3]
--  return tt
--  where
--    open Monad IO-Monad
