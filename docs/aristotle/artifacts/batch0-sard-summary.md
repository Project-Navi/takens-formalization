# Summary of changes
## Sard's Theorem Formalization

I formalized Sard's theorem in Lean 4 with Mathlib in `RequestProject/Sard.lean`. The formalization covers the full statement and proves all cases except the hardest one (finrank E > finrank F).

### What was proved (sorry-free)

1. **`sard_equidimensional`** — The core equidimensional case: for any C¹ map `f : E → E` between finite-dimensional real normed spaces, the image of the critical set (points where the derivative is not surjective) has additive Haar measure zero. The proof uses the area formula (Jacobian change-of-variables inequality) from Mathlib.

2. **`addHaar_image_eq_zero_of_finrank_lt`** — The low-dimensional case: the image of any set under a C¹ map from a space of strictly lower dimension has measure zero. Proved using Hausdorff dimension bounds for Lipschitz images.

3. **`sard_of_finrank_eq`** — Sard's theorem for maps between spaces of equal finite dimension, reduced to the equidimensional case via `ContinuousLinearEquiv.ofFinrankEq`.

4. **Helper lemmas**: `det_fderiv_eq_zero_of_not_surjective`, `isClosed_criticalSet`, `dimH_le_finrank`, `lipschitzOnWith_closedBall_of_contDiff`, `criticalSet_comp_linearEquiv`, `addHaar_range_eq_zero_of_finrank_lt`.

### What remains as sorry

5. **`sard_of_finrank_gt`** — The case when `finrank E > finrank F`. This is the genuinely hardest part of Sard's theorem, requiring:
   - Strong induction on `finrank E`
   - The implicit function theorem to reduce dimension at "shallow" critical points
   - Multivariate Taylor remainder estimates for "deep" critical points where all derivatives up to high order vanish
   - Careful covering arguments and stratification of the critical set

   This case cannot be reduced to the equidimensional case (the projection of a measure-zero set in a product space can have positive measure in a factor). The standard proof is several pages long even informally, and its formalization would require substantial additional infrastructure.

### Main theorem

The general `sard` theorem is stated for C^∞ maps `f : E → F` between arbitrary finite-dimensional real normed spaces and reduces to the three cases above. It depends on `sorry` only through `sard_of_finrank_gt`.

All proven theorems use only standard axioms (`propext`, `Classical.choice`, `Quot.sound`).