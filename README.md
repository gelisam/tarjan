This repo is to implement [Tarjan's algorithm](https://en.wikipedia.org/wiki/Tarjan%27s_strongly_connected_components_algorithm) in Agda. It's an algorithm which takes a graph and divides it into its strongly-connected components.

This is inspired from [a challenge from @catnaroek](https://twitter.com/catnaroek/status/1356847771765116928):

1. Implement the real algorithm, with the correct asymptotic complexity. This probably implies that we must use immutable arrays, which are uncommon in Agda (we usually prefer to use immutable length-indexed vectors).
2. Don't perform a runtime check if one is not required. In particular, because of the design of the algorithm, [this `pop` call](https://github.com/kevin-wayne/algs4/blob/master/src/main/java/edu/princeton/cs/algs4/TarjanSCC.java#L97) is always guaranteed to succeed, so we don't need to check whether the stack is empty.

Our approach is:

1. import Haskell's mutable arrays and integers via the FFI
2. transliterate the Java implementation linked above into Agda using do-notation
3. keep track of the stack's contents using an indexed IO monad
4. erase that tracking information from runtime using `@erased` annotations

The first two steps are technically sufficient to satisfy the two requirements of the challenge: it's the same algorithm, implemented using mutable arrays, and since we are using unsafe array-indexing calls, no runtime checks are performed. The third step is required in order to also satisfy the _spirit_ of the challenge, which is not just about avoiding a runtime check, but about using the type checker to guarantee that no runtime check is necessary. Finally, the fourth step prevents the third step from having an impact on the asymptotic complexity.

## Proof 1

Here is a pen-and-paper version of an easier version of the proof.

By induction, assume that the net effect of each recursive calls to `dfs` is to push zero or more values onto the stack. We now need to prove that the `dfs` call which makes those recursive calls also has this net effect. It first pushes `v` onto the stack, then performs a number of recursive calls which may push more values. Then, `dfs` may returns early, in which case the condition is satisfied because so far it has only pushed. Otherwise, `dfs` pops all the values from the stack until it pops `v`, in which case the condition is also satisfied because the stack is exactly as it was at the beginning of the call.

Note that `v` is still on the stack when we call `pop`, and therefore the stack is non-empty and so the call is safe.

## Proof 2

The above proof assumes that `dfs` pops all the values from the stack until it pops the `v` it initially pushed onto the stack. The code does that by popping values until the popped value is equal to `v`, which in practice will be that same `v` because the algorithm never pushes the same value onto the stack. I would prefer not to also have to prove that the algorithm never pushes the same value onto the stack, and fortunately, I don't have to, because the proof still goes through in the counter-factual case in which a different `v` is popped:

...Otherwise, `dfs` pops some values from the stack until it pops a `v`. Since a `v` was pushed onto the stack at the very beginning of the `dfs` call, that `v` acts as a guard which guarantees that we stop popping before we touch anything which was on the stack before the `dfs` call began. Thus, any of the values we have popped must be values which have been pushed during the `dfs` call, and thus its net effect is to push zero or more values, as desired.
