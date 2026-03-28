# Summary of changes
Both theorems in `batch1-sard-low-dim.lean` have been formally proved and verified:

1. **`addHaar_image_eq_zero_of_finrank_lt`**: For a C¹ map `f : E → F` between finite-dimensional real normed spaces with `finrank ℝ E < finrank ℝ F`, the image `f '' s` of any set `s` has additive Haar measure zero in `F`.

2. **`addHaar_range_eq_zero_of_finrank_lt`** (corollary): The range of such a map has measure zero.

**Proof strategy** (for the main theorem):
- A C¹ map is locally Lipschitz (`ContDiff.locallyLipschitz`).
- Locally Lipschitz maps don't increase Hausdorff dimension (`dimH_image_le_of_locally_lipschitzOn`), so `dimH(f '' s) ≤ dimH(s) ≤ finrank ℝ E`.
- Since `finrank ℝ E < finrank ℝ F`, we get `dimH(f '' s) < finrank ℝ F`.
- The additive Haar measure on `F` is absolutely continuous w.r.t. the Hausdorff measure of dimension `finrank ℝ F` (`Measure.absolutelyContinuous_isAddHaarMeasure`).
- Any set with Hausdorff dimension strictly less than `d` has zero `d`-dimensional Hausdorff measure, hence zero Haar measure (`measure_zero_of_dimH_lt`).

The corollary follows by rewriting `range f` as `f '' univ`.

The project builds cleanly with no `sorry`, no warnings, and only standard axioms (`propext`, `Classical.choice`, `Quot.sound`).