# Summary of changes
## Batch 0: All 12 Theorems Proved ✅

All 12 exploratory API probes in `batch0_exploration.lean` (renamed from `batch0-exploration.lean` to fix the invalid Lean module name) are now fully proved with no `sorry` remaining.

### Fixes Applied
1. **Module naming**: Renamed `batch0-exploration.lean` → `batch0_exploration.lean` (hyphens are invalid in Lean module names). Updated `lakefile.toml` accordingly.
2. **Import**: Replaced individual Mathlib imports with `import Mathlib` for full API access.
3. **Tuple.sort statements (Group 4)**: The original statements were ill-typed — `Tuple.sort v` returns an `Equiv.Perm (Fin n)`, not a sorted tuple. Corrected:
   - `tuple_sort_monotone`: Changed goal from `Monotone (Tuple.sort v)` to `Monotone (v ∘ Tuple.sort v)`
   - `tuple_sort_perm`: Changed goal to use `v ∘ Tuple.sort v` instead of `Tuple.sort v` as a function to ℝ
4. **Cleaned up `exact?`**: Replaced all `exact?` placeholders with their resolved proof terms.

### Results by Group

| Group | Theorem | Status |
|-------|---------|--------|
| **1: Period semantics** | `isPeriodicPt_of_bijective` | ✅ `isPeriodicPt_minimalPeriod` |
| | `minimalPeriod_pos_of_bijective` | ✅ Pigeonhole argument |
| | `iterate_minimalPeriod_eq` | ✅ Direct from `IsPeriodicPt` |
| | `iterate_mod_minimalPeriod` | ✅ Induction + simp |
| **2: Iterate arithmetic** | `iterate_add_apply` | ✅ `Function.iterate_add_apply` |
| | `injective_iterate` | ✅ `Injective.iterate` |
| | `iterate_zero_eq_of_all_eq_of_bijective` | ✅ `h 0` with positivity |
| **3: Orbit bounding** | `iterate_range_image_card_le` | ✅ `Finset.card_le_univ` |
| | `minimalPeriod_le_card_of_bijective` | ✅ `minimalPeriod_le_card` |
| | `iterate_image_card_le_card` | ✅ Delegates to above |
| **4: Tuple.sort** | `tuple_sort_monotone` | ✅ `Tuple.monotone_sort` |
| | `tuple_sort_perm` | ✅ `⟨_, fun i => rfl⟩` |

### Project Approach Analysis

This project formalizes **Takens' embedding theorem** in two routes:

- **Route B (Discrete)**: The main deliverable. For a finite dynamical system `(X, f)` with injective observation `α : X → ℝ`, the delay embedding is injective when window length `k ≥ |X|`. The proof strategy is:
  1. Delay embedding equality ⟹ `α(f^[i] x) = α(f^[i] y)` for `i < k`
  2. Injectivity of `α` ⟹ `f^[i] x = f^[i] y` for `i < k`
  3. `k ≥ |X|` + `minimalPeriod_le_card` ⟹ `x = y`

  Batch 0 confirms **all key Mathlib API** for this route is available: `minimalPeriod_le_card`, `iterate_add_apply`, `Injective.iterate`, `isPeriodicPt_minimalPeriod`.

- **Route A (Smooth)**: Classical smooth Takens theorem on manifolds, gated behind a `SardInfra` axiom typeclass (Sard's theorem is not in Mathlib).

- **Ordinal Takens**: Composes Route B with Bandt-Pompe ordinal patterns. `Tuple.sort` API exists but returns a *permutation*, not a sorted tuple — definitions in `OrdinalPattern.lean` should account for this.

**Key finding**: The `Verify.lean` file imports `TakensFormal.X` modules which don't exist (files are at root level, not in a `TakensFormal/` directory). This will need fixing when building the full project. The other module files (`DelayWindow.lean`, `IteratePeriod.lean`, etc.) currently contain only docstrings with no definitions or theorems yet.