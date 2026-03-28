# Summary of changes
I formalized and proved the core theory of Bandt-Pompe ordinal patterns in `RequestProject/BandtPompe.lean`. All theorems compile without `sorry` and use only standard axioms (propext, Classical.choice, Quot.sound).

## Definitions
- **`IsOrdinalPatternOf σ f`**: A permutation `σ` is an ordinal pattern of `f : Fin d → ℝ` if `f ∘ σ` is strictly monotone (i.e., `σ` sorts the values of `f`).
- **`ordinalPatternOf f hf`**: The unique ordinal pattern of an injective function `f`.
- **`timeSeriesWindow x d t`**: The sliding window `(x(t), x(t+1), ..., x(t+d-1))` for time series analysis.

## Theorems proved
1. **`exists_unique_ordinalPattern`**: For any injective `f : Fin d → ℝ`, there exists a unique sorting permutation — the fundamental existence and uniqueness result.
2. **`ordinalPatternOf_strictMono`**: The constructed ordinal pattern indeed makes `f ∘ σ` strictly monotone.
3. **`ordinalPattern_surjective`**: Every permutation in `Perm(Fin d)` is realizable as the ordinal pattern of some injective function (constructed via `f(i) = σ⁻¹(i)`).
4. **`ordinalPattern_monotone_invariant`**: Ordinal patterns are invariant under strictly monotone transformations — they capture only relative ordering, not magnitudes.
5. **`card_ordinalPatterns`**: The number of ordinal patterns of order `d` equals `d!`.
6. **`timeSeriesPattern_wellDefined`**: Ordinal patterns are well-defined for time series windows with distinct values.
7. **`ordinalPattern_id_iff`**: The identity permutation is the ordinal pattern iff the function is already strictly monotone.
8. **`ordinalPattern_unique`**: If two permutations both sort the same function, they must be equal.