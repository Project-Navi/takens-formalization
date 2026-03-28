# Summary of changes
Both theorems in `batch1-orbit-separation.lean` have been proved:

1. **`delay_image_card_le`**: Shows that `(Finset.univ.image delayMap).card ≤ Fintype.card X` using `Finset.card_image_le` (the image of a finset has at most as many elements as the original finset) combined with `Finset.card_univ`.

2. **`card_le_of_injective_delay`**: Shows that if the delay map is injective, then `Fintype.card X ≤ (Finset.univ.image delayMap).card`, using `Finset.card_image_of_injective` (an injective function preserves finset cardinality under image) and `Finset.card_univ`.

The file builds successfully with no `sorry` statements and no non-standard axioms.