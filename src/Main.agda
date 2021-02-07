{-# OPTIONS --no-termination --type-in-type #-}
module Main where

open import Data.Unit
  using (⊤; tt)

open import Array
open import Bool
open import Graph
open import IORef
open import Int
open import IxIO
open import Linked
open import Monad
open import SimpleIO
open import Step


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
    push : {@erased xs : List Int}
         → (x : Int) → IxIO xs (x ∷ xs) ⊤
    push v = UnsafeIxIO do
      i ← readIORef stack-size
      stack [ i ]≔ v
      modifyIORef stack-size succ

    pop : {@erased x : Int} {@erased xs : List Int}
        → IxIO (x ∷ xs) xs (Linked x)
    pop {x} = UnsafeIxIO do
      modifyIORef stack-size pred
      i ← readIORef stack-size
      actual ← stack [ i ]
      return (unsafeLinked x actual)

    -- int w;
    -- do {
    --     w = stack.pop();
    --     id[w] = count;
    --     low[w] = G.V();
    -- } while (w != v);
    -- count++;
    dfsWhile : (v : Int) → IxIO tt tt ⊤
    dfsWhile v = do
      -- w , _ ← pop
      --count-value ← lift (readIORef count)
      --lift (id [ w ]≔ count-value)
      --lift (low [ w ]≔ n)
      --if w == v
      --  then lift (modifyIORef count succ)
      --  else dfsWhile v
      return tt

    mutual
      -- for (int w : G.adj(v)) {
      --     if (!marked[w]) dfs(G, w);
      --     if (low[w] < min) min = low[w];
      -- }
      -- if (min < low[v]) {
      --     low[v] = min;
      --     return;
      -- }
      -- do {...}
      dfsFor : IORef Int
             → Int
             → List Node
             → IxIO tt tt ⊤
      dfsFor min v (w ∷ out-edges) = do
        w-marked? ← lift (marked [ w ])
        ixWhen (not w-marked?) (dfs w)
        low[w] ← lift (low [ w ])
        min-value ← lift (readIORef min)
        lift (when (low[w] < min-value) (writeIORef min low[w]))
        dfsFor min v out-edges
      dfsFor min v [] = do
        min-value ← lift (readIORef min)
        low[v] ← lift (low [ v ])
        if (min-value < low[v])
          then lift (low [ v ]≔ min-value)
          else dfsWhile v

      -- marked[v] = true;
      -- low[v] = pre++;
      -- int min = low[v];
      -- stack.push(v);
      -- for (int w : G.adj(v)) {...}
      dfs : Int → IxIO tt tt ⊤
      dfs v = do
        lift (marked [ v ]≔ true)
        low[v] ← lift (readIORef pre)
        lift (low [ v ]≔ low[v])
        lift (modifyIORef pre succ)
        min ← lift (newIORef low[v])
        --push v
        out-edges ← lift (g [ v ])
        dfsFor min v out-edges

    -- for (int v = 0; v < G.V(); v++) {
    --     if (!marked[v]) dfs(G, v);
    -- }
    tarjanFor : Int → IO ⊤
    tarjanFor v = do
      when (v < n) do
        v-marked? ← marked [ v ]
        when (not v-marked?) (runIxIO (dfs v))
        tarjanFor (succ v)

  -- marked = new boolean[G.V()];
  -- stack = new Stack<Integer>();
  -- id = new int[G.V()]; 
  -- low = new int[G.V()];
  -- for (int v = 0; ...) {...}
  tarjan : IO (Array Int)
  tarjan = do
    marked ← newArray n false
    stack ← newArray n (fromℕ 0)
    stack-size ← newIORef (fromℕ 0)
    id ← newArray n (fromℕ 0)
    low ← newArray n (fromℕ 0)
    pre ← newIORef (fromℕ 0)
    count ← newIORef (fromℕ 0)
    tarjanFor marked id low stack stack-size pre count (fromℕ 0)
    return id

main : IO ⊤
main = do
  g ← mkExampleGraph
  r ← tarjan g
  printIntArray r -- should be [0,0,0,2,2,1,1,3]
  return tt
