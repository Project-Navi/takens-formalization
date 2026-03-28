# Summary of changes
Successfully formalized and proved all requested results in `RequestProject/DelayCoordinate.lean`. The file contains five main results, all fully proven (no `sorry`), using only standard axioms (`propext`, `Classical.choice`, `Quot.sound`):

### General theory (compact → Hausdorff)
1. **`compactToT2_isClosedEmbedding`**: A continuous injection from a compact space to a Hausdorff space is a closed embedding. (Wraps Mathlib's `Continuous.isClosedEmbedding`.)
2. **`compactToT2_rangeHomeomorph`**: The range factorization of such a map is a homeomorphism `X ≃ₜ Set.range f`. (Constructed via `Equiv.ofInjective` lifted to a homeomorphism using the inducing property.)

### Delay coordinate map application
3. **`delayCoordinateMap`** (definition): `fun x i => h (T^[i] x) : X → (Fin n → ℝ)`.
4. **`delayCoordinateMap_continuous`**: Continuous when `T` and `h` are continuous (via `continuous_pi` and `Continuous.iterate`).
5. **`delayCoordinateMap_isClosedEmbedding`**: If the delay coordinate map is injective on a compact space, it is a closed embedding into `Fin n → ℝ` (which is T₂).
6. **`delayCoordinateMap_rangeHomeomorph`**: Under the same hypotheses, the range factorization is a homeomorphism onto its image.