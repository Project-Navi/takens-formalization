# Summary of changes
All three theorems in `batch1-compact-embedding.lean` have been proved:

1. **`isClosedEmbedding_of_continuous_injective_compact_t2`** — A continuous injection from a compact space to a T2 space is a closed embedding. This follows directly from Mathlib's `Continuous.isClosedEmbedding`.

2. **`isEmbedding_of_continuous_injective_compact_t2`** — A continuous injection from a compact space to a T2 space is an embedding. Derived from the closed embedding result via `IsClosedEmbedding.isEmbedding`.

3. **`isHomeomorph_of_continuous_bijective_compact_t2`** — A continuous bijection from a compact space to a T2 space is a homeomorphism. Proved by constructing `IsHomeomorph` directly: continuity is given, surjectivity comes from bijectivity, and openness of the map is shown by proving that images of open sets have closed complements (using compactness and Hausdorffness).

All proofs compile without `sorry` or non-standard axioms, using Mathlib's `IsClosedEmbedding` and `IsEmbedding` API as requested.