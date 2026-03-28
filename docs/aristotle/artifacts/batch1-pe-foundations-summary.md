# Summary of changes
All requested theorems in `batch1-pe-foundations.lean` have been formalized and proved:

1. **`observedPatterns`** — defined as the `Finset.image` of `Tuple.sort` over `Finset.range N`, mapping each time offset `t` to the ordinal pattern of the observable `α` along the orbit `f^[t], f^[t+1], …, f^[t+d-1]` starting at `x`.

2. **`card_observedPatterns_le`** — the number of observed patterns is at most `d!`. Proved by showing the pattern set is a subset of `Finset.univ` (all permutations of `Fin d`), whose cardinality equals `d!` by `Fintype.card_perm`.

3. **`card_observedPatterns_le_N`** — the number of observed patterns is at most `N`. Proved directly via `Finset.card_image_le` applied to `Finset.range N`.

4. **`card_observedPatterns_le_period'`** (corrected version) — on a periodic orbit, the number of distinct patterns is at most the minimal period `p`. Proved by showing the image over `range N` is contained in the image over `range p` (since iterates at congruent times mod `p` agree), then applying `card_le_card` and `card_image_le`.

**Note on the original `card_observedPatterns_le_period`:** The original statement (without a periodicity hypothesis) is false — when `x` is not periodic, `minimalPeriod f x = 0` but the pattern set can be nonempty. The original statement has been commented out with an explanation, and a corrected version (`card_observedPatterns_le_period'`) with hypothesis `hx : x ∈ periodicPts f` is provided and proved.

A helper lemma `iterate_mod_minimalPeriod` (iterates at congruent times agree on periodic orbits) was also formalized and proved.