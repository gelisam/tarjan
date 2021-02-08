The goal of this repo is to implement [Tarjan's algorithm](https://en.wikipedia.org/wiki/Tarjan%27s_strongly_connected_components_algorithm) in Agda. It's an algorithm which takes a graph and divides it into its strongly-connected components.

This is inspired from [a challenge from @catnaroek](https://twitter.com/catnaroek/status/1356847771765116928):

1. Implement the real algorithm, with the correct asymptotic complexity. This probably implies that we must use immutable arrays, which are uncommon in Agda (we usually prefer to use immutable length-indexed vectors).
2. Don't perform a runtime check if one is not required. In particular, because of the design of the algorithm, [this `pop` call](https://github.com/kevin-wayne/algs4/blob/master/src/main/java/edu/princeton/cs/algs4/TarjanSCC.java#L97) is always guaranteed to succeed, so we don't need to check whether the stack is empty.

Our current approach is to define mutable arrays and integers using the Haskell FFI, and to transliterate the Java implementation linked above into Agda using do-notation.

The above two conditions are technically already satisfied: it's the same algorithm, implemented using mutable arrays, and since we are using unsafe array-indexing calls, no runtime checks are performed. However, we are not yet satisfying the _spirit_ of the challenge, which is about using the type checker to guarantee that the `pop` call is safe. To do that, our plan is to use the approach described in Conor McBride's paper "[Kleisli arrows of outrageous fortune](https://personal.cis.strath.ac.uk/conor.mcbride/Kleisli.pdf)".

I have barely started reading the paper, but I already have a guess about its main idea: switch from Monad to Arrow, and use predicates about the input and outputs to guarantee what we need. More formally, each object `(A, p)` in the category is a type `A` and a predicate `p : A -> Set`, and a morphism from `(A, p)` to `(B, q)` is a computation of type `∃ p → IO (∃ q)`. That is, a morphism takes an `a : A` and a proof of `p a`, performs some side-effects, and returns a `b : B` and a proof of `q b`.

Here is a pen-and-paper version of the proof we want to formalize. By induction, assume that the net effect of each recursive calls to `dfs` is to push zero or more values onto the stack. We now need to prove that the `dfs` call which makes those recursive calls also has this net effect. It first pushes `v` onto the stack, then performs a number of recursive calls which may push more values. Then, `dfs` may returns early, in which case the condition is satisfied because so far it has only pushed. Otherwise, `dfs` pops all the values from the stack until it pops `v`, in which case the condition is also satisfied because the stack is exactly as it was at the beginning of the call.
