# Summary of changes
Both theorems in `batch1-window-distinct.lean` have been fully proven:

1. **`windowDistinct_of_injective_orbit`**: If `α` is injective and the orbit of `x` under `f` is injective on `Fin k`, then the delay window `fun i => α(f^[i] x)` is injective. The proof works by composing the two injectivity hypotheses.

2. **`orbit_injective_of_injective`**: If `f` is injective and `f^[i] x = f^[j] x`, then either `i = j` or there exists a positive period `p` such that `f^[p] x = x` (with `i = j + p` or `j = i + p`). The proof uses trichotomy on `i` vs `j`, then applies `Function.Injective.iterate` and `Function.iterate_add_apply` to extract the periodic witness.

Both proofs compile cleanly with no `sorry` and only standard axioms (`propext`, `Classical.choice`, `Quot.sound`).