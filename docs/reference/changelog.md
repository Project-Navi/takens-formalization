# Changelog

Research milestones in the formalization of Takens' delay embedding theorem.
Entries are mathematical events, not infrastructure commits.

---

### 2026-03-31

- **Launched documentation site** -- Scaffolded the Zensical-based docs site with brand assets, proof architecture diagram, and reference page stubs.

### 2026-03-28

- **Proved `sard_equidim` and `sard_low_dim`** -- Sard's theorem for the equidimensional case (via the Jacobian area formula) and the low-dimensional case (via Hausdorff dimension). Also proved `sard_equidim_general` reducing the general equidimensional case to the endomorphism case via continuous linear equivalence. Reached 42 declarations, zero sorry.
- **Proved observed-pattern cardinality bounds** -- `card_observedPatterns_le_factorial` ($\le d!$), `card_observedPatterns_le_length` ($\le N$), and `card_observedPatterns_le_period` ($\le \text{minPeriod}$). These are the formal foundations for permutation entropy analysis.
- **Defined `coincidenceLength` and proved `exists_separatingWindow_iff`** -- Novel contribution: a non-injective observation can yield an injective delay embedding iff orbits eventually disagree. On finite types, the window length is bounded by the maximum first-disagreement index.
- **Proved `det_fderiv_eq_zero_of_not_surjective` and `surjective_iff_det_ne_zero`** -- Structural lemmas connecting the critical set to the zero-determinant locus. Foundation for the Sard proofs.
- **Proved `separatesOrbits_of_injective` and period-based window distinctness** -- Bridge lemmas connecting orbit separation to Mathlib's `minimalPeriod` API.
- **Proved `smoothDelayMap_isClosedEmbedding` and `smoothDelayMap_rangeHomeomorph`** -- Complete Route A embedding chain: continuous + injective on compact space implies closed embedding and homeomorphism onto image. Axiom-free (does not import `SardInfra`).
- **Initial scaffold** -- `delayEmbedding`, `SeparatesOrbits`, `delayEmbedding_injective_iff_separatesOrbits` (Route B headline), `ordinalPattern` with existence/uniqueness/surjectivity, `ordinalDelayMap` with monotone invariance. All zero sorry from the first commit.
