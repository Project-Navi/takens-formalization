# AGENTS.md — Lean 4 + Mathlib conventions

Shared conventions for Lean 4 formalization repos, adapted for this repository
(`TakensFormal`). Task-specific proof obligations take precedence over these generic
conventions. Keep the Lean formalization repos on one Lean and Mathlib release where
possible, so lemmas can be ported between them without a bump; this repo pins `v4.34.1`.
API notes below were checked against that pin; re-check them after a bump.

## Invariants

- **No `sorry` on the default branch.** Every declaration is fully proved before merge.
- **No `axiom` declarations.** A classical result that is not proved is not a theorem of
  this repository; it is reported as missing.
- **Axiom allowlist**: every selected result depends only on `propext`, `Classical.choice`
  and `Quot.sound`. Anything else, including `sorryAx`, is a failure.
- **Every module compiles.** `lake build` builds only what the root imports, so a file
  nobody imports is never checked and can rot silently. CI builds every tracked module,
  and the source check requires the root `TakensFormal.lean` to import every library module.
- **No unproved infrastructure assumptions.** No typeclass or structure carries an unproved
  result into a headline theorem, and CI rejects `...Infra` classes. A Prop-valued class is
  fine when every instance the results use is proved, as for `ClosedBallCoveringMeasure` in
  the Sard port (Besicovitch and doubling-measure instances). Never complete a proof
  by adding an unproved hypothesis, field, or equivalent assumption. A clean axiom report
  does not discharge theorem hypotheses: report the complete signature.
- **No vacuous assumptions.** Never encode an open problem or a missing proof as `True`,
  an unconstrained `Nonempty` witness, or an arbitrary `Type` or `TopologicalSpace` the
  statement gets to choose. An assumption is a concrete proposition about the actual
  mathematical objects, or it is not there.

## Build & verify

```bash
lake exe cache get                                   # Mathlib oleans; never build Mathlib
make build      # lake build --wfail of every tracked module (warnings are errors)
make lint       # lake lint (Mathlib environment linters)
make audit      # scripts/check_source.py: placeholders, headers, imports
make verify     # axiom records, documented names, fresh kernel replay
make test-checkers                                   # negative tests of the checkers
lake env lean -DwarningAsError=true TakensFormal/Examples.lean   # worked examples
make docs-check                                      # zensical build + link check
```

- If the sandbox cannot install Lean or fetch the Mathlib cache, push to a draft PR and
  let CI build and verify. Report which checks ran where; never claim a local build that
  did not happen.
- `TakensFormal/Verify.lean` holds exactly one `#print axioms` per selected declaration:
  every headline result and every project declaration the docs cite. Add a line when you
  add one of those. `scripts/check_axioms.py` requires one record per line, in order,
  within the allowlist, and rejects empty, missing, duplicate, extra and renamed records
  and hidden Lean failures.
- `scripts/check_doc_names.py` resolves every Lean name cited in the README and docs with
  Lean itself and requires cited project declarations to be selected in `Verify.lean`.
- `scripts/check_source.py` rejects `sorry`, `admit`, native evaluation (`native_decide`,
  `decide +native`), trust-extending names and options (also when qualified, as in
  `Lean.ofReduceBool`), `axiom` declarations, `#exit`, `...Infra` classes, bare `import Mathlib`, missing
  headers, and wrong import directions (see *File layout*).
- `scripts/test_checkers.py --lean` feeds the checkers small failing fixtures (including
  real Lean runs) and snapshots of accepted output. When you add or change a gate, add a
  fixture that must fail it.
- Independent kernel replay: `lake env leanchecker --fresh TakensFormal` re-checks every
  declaration in the library's import closure in a fresh kernel.
- Change `lake-manifest.json` only in an intentional dependency bump, in its own commit.
- CI (`.github/workflows/lean_action_ci.yml`, required check `build`) runs, from a fresh
  checkout with only Mathlib's cache: the source check, the strict build of every tracked
  module, the examples, `lake lint`, the axiom check, the documented-names check, the checker
  tests and the fresh kernel replay. The docs workflow (check `docs`) builds the site and
  checks its links on every PR, and deploys Pages only for a push or manual run on `main`.

## Project configuration

- Lean options live in `lakefile.toml` `[leanOptions]`, the single source of truth:
  ```toml
  [leanOptions]
  pp.unicode.fun = true
  relaxedAutoImplicit = false
  autoImplicit = false
  maxHeartbeats = 200000
  weak.linter.mathlibStandardSet = true
  weak.linter.style.longLine = true
  weak.linter.style.lambdaSyntax = true
  weak.linter.style.dollarSyntax = true
  weak.linter.style.cdot = true
  weak.linter.style.missingEnd = true
  ```
  Do not add per-file `set_option` for them. The one exception is the vendored port (see
  *File layout*).
- `lintDriver = "batteries/runLinter"`.
- Mathlib is required at a release tag (`rev = "v4.34.1"`), with no local fork and no
  `require` overrides. Bump only when a needed API landed or changed, in an isolated commit.

## File layout

Every `.lean` file, in order:

1. Copyright header, matching the repository's `LICENSE` and actual contributors:
   ```lean
   /-
   Copyright (c) 2026 Nelson Spence. All rights reserved.
   Released under Apache 2.0 license as described in the file LICENSE.
   Authors: Nelson Spence
   -/
   ```
2. Granular imports. **Never `import Mathlib`.**
3. Module docstring `/-! ... -/`: title, summary, `## Main definitions`,
   `## Main statements`, `## Implementation notes`, `## References`, `## Tags`.

- `TakensFormal/` holds the project modules; `TakensFormal.lean` imports all of them.
- `TakensFormal/ForMathlib/` is the general-purpose layer: it imports only Mathlib and
  other `ForMathlib` modules, never a project module. CI checks this import direction.
- `TakensFormal/ForMathlib/SardMoreira/` is a port of part of the SardMoreira project
  (Apache 2.0). Its files keep the upstream copyright line (CI checks it), record the
  source file and commit in a `## Provenance` section, and say what changed. Mathlib's
  proof-style linters are switched off at the top of each ported file so the proofs stay
  close to upstream. Do not restyle them without a reason; do not copy more of the
  upstream project than a proof needs. `Chart`, `ChartEstimates` and `MainTheorem` also set
  `backward.isDefEq.respectTransparency false`, the unification behaviour of the Lean
  release the proofs were written for; no module outside the port sets it.
- `TakensFormal/Verify.lean` (axiom dashboard) and `TakensFormal/Examples.lean` (worked
  examples, `#guard` checks) are diagnostic: the root does not import them and no library
  module may import them. CI builds and runs both.
- There is no `Experimental/` directory. Unfinished work does not land on the default
  branch.
- Keep files under ~1000 lines and split along natural boundaries.
- Every `def` has a `/-- ... -/` docstring (the `docBlame` linter checks this).
- Cite references as `[AuthorYear]`, with entries in `docs/references.bib`.

## Naming (Mathlib)

- Theorems (Prop terms): `snake_case`, e.g. `separatingHorizon_le_card_sub_one`.
- Types, structures, classes, Props-as-types: `UpperCamelCase`, e.g.
  `IsContMDiffEmbedding`.
- Other terms (defs, functions, instances): `lowerCamelCase`, e.g. `delayEmbedding`.
- An UpperCamelCase name inside snake_case becomes lowerCamelCase: `neZero_iff`.
- Conclusion first, hypotheses joined by `_of_` in order: `C_of_A_of_B` for `A → B → C`.
- American English (`factorization`).
- No Greek letters in declaration names; spell them out (`sigma`, not `σ`).
- Never shadow prelude names with variables (`le`, `lt`, `eq`, `ne`).
- Standard parameters here: `{X : Type*}`, `(f : X → X)` dynamics, `(α : X → Y)`
  observation, `(k : ℕ)` window length; on manifolds `(T : M → M)`, `(h : M → ℝ)`.

## Formatting

- 100-character lines.
- `by` at the end of the preceding line, never on its own line.
- 2-space indent for proof bodies; 4-space for continuation lines of a statement.
- No blank lines inside a declaration.
- Focusing dots `·` flush with the current indent, with the tactics beneath them.
- `:`, `:=` and infix operators end a line; they don't start the next one.
- `fun x ↦`, not `λ`. No `$`; use `<|`.
- One tactic per line. Semicolons are only for a short sequence that expresses one idea.

## Definitions and statements

- `Type*`, not `Type _`.
- `where` syntax for instances, not braces.
- Hypotheses go left of the colon: `(h : 1 < n) : 0 < n`, not `: 1 < n → 0 < n`.
- `abbrev` and `@[irreducible]` each need a stated justification.
- Classical by default. Don't thread `Decidable` instances unless the type demands them
  (executable procedures such as `horizonSearch` do).
- Regularity exponents have type `WithTop ℕ∞`: a finite `n` is `C^n`, `∞` (that is
  `((⊤ : ℕ∞) : WithTop ℕ∞)`) is `C^∞`, and `ω = ⊤` is analyticity. Never write `⊤` for
  "smooth". State finite regularity (`2` for `C²`) where a theorem needs it.
- When unifying two definitions, keep the old name as a definition or deprecated alias
  with a proved equality, so existing statements keep their meaning.

## Attributes

- `@[simp]` on equations or iffs whose LHS is more complex than the RHS. It must not loop.
- `@[ext]` on extensionality lemmas; `@[simps]` for structure projections.
- `@[gcongr]` on congruence lemmas of the form `f x₁ ∼ f x₂` given `x₁ ∼ x₂`.

## Tactics

| Goal | Reach for |
|------|-----------|
| Linear ℕ/ℤ arithmetic | `omega` |
| Numerals | `norm_num` |
| Decidable props | `decide` |
| `0 ≤ x`, `0 < x` | `positivity` |
| Monotonicity / congruence | `gcongr` |
| Nonlinear arithmetic | `nlinarith [hints]` |
| ℕ subtraction | `zify [h₁, h₂]` first |
| Field algebra | `field_simp`, then `ring` or `linarith` |
| General rewriting | `simp` (last resort) |

- A terminal `simp` stays unsqueezed, since squeezed lists break on lemma renames.
- A non-terminal `simp` must be `simp only [...]`.
- `aesop` only with explicit local rule sets, or replaced by the script `aesop?` produces.
- When a `simp` call leaves an unexpected residual goal, an explicit
  `rw [defn, lemma₁, lemma₂]` chain is often more robust.
- `exact?`, `apply?` and `simp?` are for exploration only. Never commit them.

## API notes (Mathlib v4.34.1)

**Casts, ℕ and iteration**
- `exact_mod_cast` settles `↑n` vs `n` mismatches; after `Nat.cast_sub`, normalize with
  `simp only [Nat.cast_ofNat, Nat.cast_one]` before `linarith`.
- `exact_mod_cast` does not beta-reduce the hypothesis: for
  `h : (fun l ↦ ((l : ℕ) : ℝ)) a = (fun l ↦ ((l : ℕ) : ℝ)) b` use `Nat.cast_injective h`.
- In `fun l ↦ ((l : ℕ) : ℝ)` the ascription fixes the binder type to `ℕ`; annotate the binder
  (`fun l : Fin L ↦ ((l : ℕ) : ℝ)`).
- `ring` does not close `a * a ^ n = a ^ (n + 1)` on ℕ; use `rw [pow_succ, mul_comm]`.
- `omega` does not see `Fin` value facts; state them first.
- `Function.iterate_succ_apply'` unfolds `f^[n+1] x = f (f^[n] x)` from the right.
- Periodic points live in `Mathlib.Dynamics.PeriodicPts.Defs` (`Function.minimalPeriod`,
  `Function.IsPeriodicPt`).

**Renames met moving from v4.28.0**
- `if_pos` / `if_neg` and `dif_pos` / `dif_neg` are deprecated; `ite_eq_left` /
  `ite_eq_right` and `dite_eq_left` / `dite_eq_right`.
- `Polynomial.eval_finset_sum` and `Polynomial.finset_sum_coeff` are `eval_finsetSum` and
  `finsetSum_coeff`.
- `ContinuousLinearMap.smul_apply`, `sub_apply` and `sum_apply` are deprecated for the
  generic `smul_apply`, `sub_apply` and `sum_apply`; write `_root_.smul_apply` when the
  namespace `MeasureTheory.Measure` is open. `ContinuousLinearMap.lipschitz` is
  `lipschitzWith`.
- `HasFDerivAt.add` concludes about `f + g`; the lambda form `fun x ↦ f x + g x` is
  `HasFDerivAt.fun_add`.
- `push_neg` is deprecated; `push Not`.
- `Mathlib.Data.Real.Basic` moved to `Mathlib.Basic.Real.Basic`, `Mathlib.Data.ENNReal.*`
  to `Mathlib.Basic.ENNReal.*`; `Mathlib.Data.Real.StarOrdered` is deprecated.
- Set difference lemmas use `sdiff` (`sdiff_subset`, `sdiff_eq`, `measure_inter_add_sdiff`);
  set-builder lemmas use `ofPred` (`Set.mem_ofPred_eq`, `Set.ofPred_and`).
- a.e. equality and inclusion of *sets* are `Filter.EventuallyEqSet` and
  `Filter.EventuallySubset` (still written `=ᵐ[μ]`, `≤ᵐ[μ]`); `rw [EventuallyEq]` no longer
  unfolds them. `(h : s ⊆ t).eventuallyLE` is deprecated in favour of
  `LE.le.eventuallySubset`.
- `StrictMono.range_inj` is `StrictMono.range_inj_of_wellFoundedLT`;
  `OpenPartialHomeomorph.symm_mapsTo` is `OpenPartialHomeomorph.mapsTo_symm`;
  `fderiv_comp'` is `fderiv_fun_comp`; `ContinuousLinearMap.coe_comp'` is `coe_comp`.
- `simp` no longer eta-reduces or merges pointwise differences like
  `fun i ↦ f i - g i`; combine coordinate big-O estimates with `isBigO_pi` first.
- The setOption linter rejects unscoped `set_option linter.* false`; scope it with `in`,
  or (only in the vendored port) switch off `linter.style.setOption` first.
- Using `show` to change the goal is flagged by a linter; use `change`.

**Calculus and manifolds**
- `ContDiff.continuous_fderiv` and `ContDiffAt.differentiableAt` take `(hn : n ≠ 0)`;
  use `one_ne_zero` for `C¹`.
- `ContDiff` at `n = ⊤` reduces to an existential, so dot notation (`.comp`) can fail.
  Call `ContDiff.comp hg hf` as a function.
- `mvfderiv I g x : TangentSpace I x →L[ℝ] F` is the differential of a vector-valued map
  `g : M → F` with values in `F`; `mfderiv` lands in `TangentSpace 𝓘(ℝ, F) (g x)`, which is
  `F` only up to definitional unfolding. `TangentSpace I x` is `E` definitionally, but
  instance search does not see through it: supply
  `inferInstanceAs (FiniteDimensional ℝ E)` when needed.
- Mathlib's `IsDiffImmersionAt` is the left-inverse differential condition;
  `IsDiffImmersionAt.of_injective_of_finiteDimensional` converts from injectivity.
- The sphere and `Circle` are analytic manifolds: `contMDiff_coe_sphere`,
  `injective_mvfderiv_subtypeVal_sphere`, `ContMDiff.codRestrict_sphere`;
  `finrank_real_complex_fact'` is a theorem to use as a local instance for `ℂ`.
- Sums `∑ i, a i • mfderiv I 𝓘(ℝ, F) (g i) x v` have a summand type that depends on `i`
  (`TangentSpace 𝓘(ℝ, F) (g i x)`), and `rw` then fails ("not type-correct under the
  `implicit` transparency level"). State such conditions with `mvfderiv`, whose values lie
  in `F`.
- `ContMDiff.mdifferentiableAt` and `mfderiv_comp` need no `IsManifold` instance; the
  `unusedArguments` linter flags an unused one.
- `IsManifold I ∞ M` gives `IsManifold I n M` for numerals `n`, and `ENat.LEInfty.out`
  proves `n ≤ ∞` for `ContMDiff.of_le`.
- `HasFDerivAt.pow` has derivative `(n • f x ^ (n - 1)) • f'`.
- Whitney: `exists_embedding_euclidean_of_compact` gives a smooth injective immersion of a
  compact manifold into some `EuclideanSpace ℝ (Fin n)`.
- If an argument must be recovered from projections of a pair, pass it explicitly
  (`hspan (a, b) hw`, not `hspan _ hw`); leaving it to unification can time out.
- Implicit function theorem for maps into finite-dimensional spaces:
  `HasStrictFDerivAt.implicitFunction`, `eq_implicitFunction`, `to_implicitFunction`.

**Measure and dimension**
- Area formula: `MeasureTheory.addHaar_image_le_lintegral_abs_det_fderiv`.
- `dimH`, `hausdorffMeasure_of_dimH_lt`, `LipschitzOnWith.dimH_image_le`,
  `DifferentiableOn.dimH_image_le` and `Real.dimH_univ_eq_finrank` are in
  `Mathlib.Topology.MetricSpace.HausdorffDimension`.
- `μH[finrank ℝ E]` is an additive Haar measure (`isAddHaarMeasure_hausdorffMeasure`), and
  `MeasureTheory.Measure.absolutelyContinuous_isAddHaarMeasure` (generated by
  `to_additive`) turns a Hausdorff-null set into a Haar-null one.
- `Measure.exists_mem_of_measure_ne_zero_of_ae` (namespace `MeasureTheory.Measure`) with
  `ae_restrict_of_ae` gives a point of a set of positive measure with an a.e. property;
  `volume` on `ι → ℝ` (finite `ι`) is an additive Haar measure.
- Lagrange interpolation: `Lagrange.interpolate s v r`,
  `Lagrange.eval_interpolate_at_node r hvs hi` (the value vector `r` is explicit) and
  `Lagrange.degree_interpolate_lt`; for root counting `Polynomial.degree_sum_fin_lt` and
  `Polynomial.card_roots'`.
- `ContDiffPointwiseHolderAt` (pointwise `C^{k+(α)}`) and `Metric.Snowflaking` are in
  Mathlib; `ContDiffPointwiseHolderAt.zero_exponent_iff` identifies exponent `0` with
  `ContDiffAt`.

## Documentation must match the code

- Every Lean name that appears in the README or docs must resolve; CI checks this.
- State hypotheses exactly as in the theorem, and state what is **not** formalized. Never
  let a theorem name or summary claim more than the statement proves. Say "not yet
  formalized here" for a classical theorem this repository has not proved.
- Keep the headline results in `Verify.lean`.

## Aristotle (automated prover)

Aristotle grinds leaf lemmas and detects dependencies. It is not the theorem architect.

- **Good targets**: cast control (ℕ → ℝ), positivity and nonzeroness, algebraic
  reshaping, `Fin` arithmetic, rpow/log/pow simplification, squeeze bounds.
- **Bad targets**: headline theorems, design decisions, anything whose definitions are
  still moving. If you can't say in one sentence why a lemma is true, don't submit it.
- **Protocol**: freeze the statement and compile it with `sorry` locally; one `sorry` per
  leaf; proof-shaped files with short helpers first; submit with `wait=False` and don't
  poll in a tight loop.
- **Output is a draft.** Keep the statement and any dependencies it discovered, then
  rewrite the proof into clean, human-owned form: granular imports, no `exact?`, no
  `axiom`, no new definitions, global `@[simp]` attributes, `maxHeartbeats` overrides or
  `pp.all`. Rebuild with `lake build --wfail`.
- Keep raw prover artifacts and run logs out of the public repository. Commit only the
  rewritten proofs.
