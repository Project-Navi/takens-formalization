# Summary of changes
Proved `det_fderiv_eq_zero_of_not_surjective` in `batch1-sard-equidimensional.lean`:

**Statement:** For a continuous linear map `L : E →L[ℝ] E` between finite-dimensional real normed spaces, if `L` is not surjective then `L.det = 0`.

**Proof strategy:** By contrapositive — assume `L.det ≠ 0`, then use `LinearMap.equivOfDetNeZero` to obtain a linear equivalence from `L`, which is injective. Then `LinearMap.surjective_of_injective` (valid in finite dimensions) gives surjectivity.

The proof compiles cleanly with no `sorry`, no warnings, and no non-standard axioms. I also fixed a lakefile issue (hyphenated module names needed quoting) and added `omit` to suppress an unused section variable linter warning.