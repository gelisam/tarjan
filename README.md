This repo implements [Tarjan's algorithm](https://en.wikipedia.org/wiki/Tarjan%27s_strongly_connected_components_algorithm) in Agda. It's an algorithm which takes a graph and divides it into its strongly-connected components.

It is inspired from [a challenge from @catnaroek](https://twitter.com/catnaroek/status/1356847771765116928):

1. Implement the real algorithm, with the correct asymptotic complexity. This probably implies that we must use immutable arrays, which are uncommon in Agda (we usually prefer to use immutable length-indexed vectors).
2. Don't perform a runtime check if one is not required. In particular, because of the design of the algorithm, [this `pop` call](https://github.com/kevin-wayne/algs4/blob/master/src/main/java/edu/princeton/cs/algs4/TarjanSCC.java#L97) is always guaranteed to succeed, so we don't need to check whether the stack is empty.

Our approach is:

1. import Haskell's mutable arrays and integers via the FFI
2. transliterate the Java implementation linked above into Agda using do-notation
3. keep track of the stack's contents using an indexed IO monad
4. erase that tracking information from runtime using `@erased` annotations

The first two steps are technically sufficient to satisfy the two requirements of the challenge: it's the same algorithm, implemented using mutable arrays, and since we are using unsafe array-indexing calls, no runtime checks are performed. The third step is required in order to also satisfy the _spirit_ of the challenge, which is not just about avoiding a runtime check, but about using the type checker to guarantee that no runtime check is necessary. Finally, the fourth step prevents the third step from having an impact on the asymptotic complexity.

## Proof

Here is a pen-and-paper version of the proof. I intentionally spell out and repeat some obvious facts in order to match the structure of the computer proof.

In the proof (but not at runtime), I represent the contents of the stack as a list, with the top of the stack being at the head of the list. So `[u] ++ xs ++ [v] ++ ys` is a stack with `u` at the top and `v` somewhere underneath. I say that `[u,v]` is a "subsequence" of `[u] ++ xs ++ [v] ++ ys`. `[v]` and `[]` are also subsequences of that list.

We want to prove that at the moment we call `pop`, the stack is non-empty. We will use induction to prove a more general statement. If we know that `vs` is a subsequence of the stack at the beginning of a call to `dfs v`, then before we call `pop` during that call, `v ∷ vs` is a subsequence and thus the stack is not empty. Furthermore, at the end of the `dfs` call, `vs` is still a subsequence of the stack.

Let us thus suppose that we know that `vs` is a subsequence of the stack at the beginning of a call to `dfs v`. The function first pushes `v` onto the stack; `v ∷ vs` is now a subsequence. Then, zero or more recursive calls to `dfs` are performed; by induction, `v ∷ vs` is still a subsequence.

At this point, the function may return early, in which case the end condition is satisfied because if `v ∷ vs` is a subsequence, then `vs` is also a subsequence, as desired.

If the function does not return early, it then pops a number of values from the stack until a `v` is popped. Before the first pop, `v ∷ vs` is a subsequence, as desired, but after the pop, there are now two possibilities: either the `v` from that subsequence is popped and `vs` is now a subsequence, or some prior entry is popped and `v ∷ vs` is still a subsequence.

To determine whether the function should keep popping, it checks if the popped value is equal to `v`. If it isn't, then we know that we are in the case in which `v ∷ vs` is still a subsequence. The loop continues, and `v ∷ vs` is still a subsequence before the next pop, as desired.

It the popped value is equal to `v`, then in practice it is going to be the `v` from the subsequence, because the algorithm only pushes a single `v` on the stack. We are thus in the other case, in which the subsequence is now `vs`, the loop terminates, and the end condition is achieved because `vs` is a subsequence.

However, since we did not prove that only one `v` exists in the stack, we must also consider the case in which the popped value is equal to `v`, but it is not the `v` from our subsequence, it is a different `v` which has been left on the stack by one of the recursive calls. In that (counter-factual) case, `v ∷ vs` is still a subsequence when the function ends, but once again, our end condition is achieved because if `v ∷ vs` is a subsequence, then `vs` is also a subsequence, as desired.
