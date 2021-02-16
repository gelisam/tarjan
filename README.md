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

## Proof 3

Agda needs every step to be spelled out, we can't say vague things like "we have only pushed so far" nor "that `v` acts as a guard". Here's a version of the proof in which a lot more steps are spelled out. We model the stack contents as a list, with the top of the stack being on the left of the list.

By induction, we want to prove that if the stack contains `zs` at the beginning of the `dfs` call, `zs` will be a suffix of the contents of the stack at the end of the call.

1. The stack initially contains `zs`.
2. `v` is pushed, so the stack now contains `[v] ++ zs`.
3. More generally, the stack now ends with `[v] ++ zs`.
4. We are now making zero or more recursive calls to `dfs`. Skip to step 8 once we're done making those calls.
3. The stack now ends with `[v] ++ zs`. In other words, the stack contains `ys ++ [v] ++ zs` for some `ys`.
5. Recursively call `dfs`. By induction, the stack now ends with `ys ++ [v] ++ ys`.
6. The stack thus also ends with `[v] ++ ys`.
7. Go to step 4.
8. The stack still ends with `[v] ++ zs`.
9. We are now popping values from the stack. This section is sometimes skipped, in which case skip to step 12.
10. Pop a value from the stack. Either the stack now contains `zs`, in which case the popped value is `v`, or the stack still ends with `[v] ++ zs`.
11. If the popped value is not `v`, the stack still ends with `[v] ++ zs`. Go to 10.
12. Otherwise the value is `v`, and the stack either contains `zs` or it ends with `[v] ++ zs`. In both cases, the stack now ends with `zs`, as desired.

These are only the steps which affect the contents of the stack. The full proof is interleaved with the implementation of the algorithm, and thus contains a lot of concrete instructions like "increment the number of strongly-connected components", accompanied by a short indication (the word `lift`) that the step does not change the contents of the stack.
