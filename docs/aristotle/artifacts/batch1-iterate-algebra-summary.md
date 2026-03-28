# Summary of changes
All four theorems in `batch1-iterate-algebra.lean` have been proved:

1. **`injective_iterate'`** — Injective `f` implies injective `f^[n]`. Proved using `hf.iterate n` (Mathlib's `Function.Injective.iterate`).

2. **`eq_of_iterate_eq_range`** — If `f^[n] x = f^[n] y` for all `n < k` with `k > 0`, then `x = y`. Proved by specializing `h` at `n = 0` (since `0 < k`) and simplifying `f^[0]` to `id`.

3. **`card_orbitFinset_le`** — The orbit finset has cardinality at most `n`. Proved via `Finset.card_image_le` (image card ≤ source card) and `Finset.card_range` (card of `range n` = `n`).

4. **`orbitFinset_card_le_card`** — On a finite type, orbit finset cardinality is at most `Fintype.card X`. Proved via `Finset.card_le_univ`.

The file builds cleanly with no `sorry` and no errors (only a manifest warning unrelated to the proofs).