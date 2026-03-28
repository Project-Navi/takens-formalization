# Summary of changes
All four theorems in `batch1-separation-finite.lean` have been formally proved and verified:

1. **`separates_iff_injective`** — An observation α : X → ℝ separates points iff it is injective. Proved by observing the two sides are definitionally equivalent.

2. **`card_range_le`** — The image of α on a finite type has cardinality at most `card X`. Proved using `Finset.card_image_le`.

3. **`injective_of_card_image_eq`** — If α achieves `card X` distinct values, then α is injective. Proved via `Finset.card_image_iff` to extract injectivity on `univ`.

4. **`separatesOrbits_of_no_coincidence`** — Contrapositive orbit separation: if every distinct pair is distinguished within k steps, then equal observations imply equal states. Proved by contraposition.

All proofs compile cleanly with no `sorry`, no custom axioms, and only standard foundational axioms (`propext`, `Classical.choice`, `Quot.sound`).