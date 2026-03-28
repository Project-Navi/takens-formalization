# Summary of changes
Both theorems in `batch1-delay-shift.lean` have been proved and the file builds successfully with no remaining `sorry`:

1. **`delayMap_comp_eq`**: Shows `delayMap f α k (f x) i = α (f^[i.val + 1] x)` — proved by `simp [delayMap]`, which unfolds the definition and automatically applies the iterate/composition simplification.

2. **`delayMap_eq_of_comp_iterate_eq`**: Shows that pointwise equality `α (f^[i] x) = β (f^[i] x)` for all `i : Fin k` implies `delayMap f α k x = delayMap f β k x` — proved by `funext fun i => h i`, directly applying the hypothesis at each index.

I also fixed a syntax issue in `lakefile.toml` (the `globs` field was malformed for the hyphenated module name).