{-# OPTIONS --no-termination --type-in-type #-}
module Main where

open import Data.Unit
  using (⊤; tt)

open import Array
open import Bool
open import Graph
open import IORef
open import Int
open import Monad
open import SimpleIO
open import IxIO


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

    pop : IO Int
    pop = do
      modifyIORef stack-size pred
      i ← readIORef stack-size
      stack [ i ]

    -- int w;
    -- do {
    --     w = stack.pop();
    --     id[w] = count;
    --     low[w] = G.V();
    -- } while (w != v);
    -- count++;
    dfsWhile : Int → IO ⊤
    dfsWhile v = do
      w ← pop
      count-value ← readIORef count
      id [ w ]≔ count-value
      low [ w ]≔ n
      if w == v
        then modifyIORef count succ
        else dfsWhile v

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
      dfsFor : IORef Int → Int → List Node → IO ⊤
      dfsFor min v (w ∷ out-edges) = do
        w-marked? ← marked [ w ]
        when (not w-marked?) (dfs w)
        low[w] ← low [ w ]
        min-value ← readIORef min
        when (low[w] < min-value) (writeIORef min low[w])
        dfsFor min v out-edges
      dfsFor min v [] = do
        min-value ← readIORef min
        low[v] ← low [ v ]
        if (min-value < low[v])
          then low [ v ]≔ min-value
          else dfsWhile v

      -- marked[v] = true;
      -- low[v] = pre++;
      -- int min = low[v];
      -- stack.push(v);
      -- for (int w : G.adj(v)) {...}
      dfs : Int → IO ⊤
      dfs v = do
        marked [ v ]≔ true
        low[v] ← readIORef pre
        low [ v ]≔ low[v]
        modifyIORef pre succ
        min ← newIORef low[v]
        runIxIO {_} {[]} {[]} (push v)
        out-edges ← g [ v ]
        dfsFor min v out-edges

    -- for (int v = 0; v < G.V(); v++) {
    --     if (!marked[v]) dfs(G, v);
    -- }
    tarjanFor : Int → IO ⊤
    tarjanFor v = do
      when (v < n) do
        v-marked? ← marked [ v ]
        when (not v-marked?) (dfs v)
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
