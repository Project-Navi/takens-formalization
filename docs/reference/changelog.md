# Changelog

Mathematical milestones in the formalization. Entries record results, not infrastructure
commits.

---

### 2026-09

- **Takens' theorem for generic pairs.** On a compact smooth \(d\)-manifold, the pairs
  \((T, h)\) of a \(C^2\) diffeomorphism and a \(C^2\) observation whose delay map with
  \(2d + 1\) coordinates is a \(C^2\) embedding are open and dense in
  \(\mathrm{Diff}^2(M) \times C^2(M, \mathbb{R})\)
  (`isOpen_and_dense_setOf_isContMDiffEmbedding_delayEmbedding_pair`). The new ingredient is
  density of bounded-period nondegeneracy and observability, a Kupka--Smale-type lemma
  (`dense_setOf_goodUpTo`), by
  induction on the period with bump perturbations in chart patches and a Fubini argument
  for almost every perturbation (`ae_forall_goodMat_perturb_comp`).
- **Good pairs are open.** The \(C^n\) topology on \(C^n\) diffeomorphisms through chart
  derivatives on source and target (`Diffeomorph.instTopologicalSpace`), first-order
  closeness preserved by composition and iteration (`BiChartWindow.exists_near_iterate`),
  and the openness of the pairs \((T, h)\) whose delay map is a \(C^2\) embedding in
  \(\mathrm{Diff}^2(M) \times C^2(M, \mathbb{R})\)
  (`isOpen_setOf_isContMDiffEmbedding_delayEmbedding_pair`).
- **Takens' theorem for a fixed map, in the \(C^2\) topology.** For an injective \(C^2\) map
  with injective differentials whose points of period at most \(4d\) are countably many and
  which is observable at points of period at most \(2d\), the observations whose delay map
  with \(2d+1\) coordinates is a \(C^2\) embedding form an open dense set
  (`isOpen_and_dense_setOf_isContMDiffEmbedding_delayEmbedding`). This rests on the weak
  \(C^n\) topology on \(C^n\) maps through chart derivatives (`JetTopology`), the stability
  of injective immersions of compact manifolds (`exists_forall_injective_of_near`), and the
  treatment of short periodic orbits by a Krylov tiling of the delayed covectors and the
  null zero sets of nonzero polynomials (`DelayPeriodic`, `MvPolynomial.ae_eval_ne_zero`).
- **Delay embeddings for maps without short periodic orbits.** On a compact smooth
  \(d\)-manifold, one finite family of smooth functions works for every injective \(C^2\)
  map with injective differentials and no periodic points of period at most \(4d\): for
  every \(C^2\) observation, Lebesgue-almost every perturbation in the family has a \(C^2\)
  delay embedding with \(2d+1\) coordinates
  (`exists_family_forall_ae_isContMDiffEmbedding_delayEmbedding`). The family comes from a
  Whitney embedding and powers of moment functionals; overlapping delay windows are handled
  by an explicit telescoping solution (`telescope_sub`).
- **Genericity in finite-dimensional families.** Almost every member of an affine family
  avoids a lower-dimensional set, is an immersion, or separates points
  (`ae_forall_ne_of_hasStrictFDerivAt`, `ae_forall_injective_fderiv_add_sum`,
  `ae_forall_add_sum_ne_add_sum`), and the corresponding statements for delay maps on
  manifolds (`ae_isContMDiffEmbedding_delayEmbedding_perturb`).
- **Sard's theorem at finite regularity in all dimensions** (`sard`), with local and
  open-set versions, by porting Yury Kudryashov's Lean proof of Moreira's theorem to the
  current Mathlib. The equidimensional and low-dimensional cases now need only \(C^1\).
- **Smooth delay maps.** Regularity, the differential and the immersion criterion; compact
  injective immersions are embeddings; the identity never immerses in dimension \(\ge 2\);
  the quarter turn of the circle as a worked example.
- **Finite state spaces.** The exact separating horizon, the sharp bound \(N-1\) on \(N \ge 1\)
  states when some window separates, with the countdown chain attaining it, a sound and complete decision procedure, and reconstruction
  of the dynamics on the delay image.
- **Ordinal codes.** Behavior under strictly decreasing transformations, empirical pattern
  entropy and its bounds, and the quotient describing what an ordinal code retains.

### 2026-03-31

- **Documentation site** --- the Zensical site with the architecture diagram and reference
  pages.

### 2026-03-28

- **Sard, equidimensional and low-dimensional cases** --- `sard_equidim` (Jacobian area
  formula), `sard_low_dim` (Hausdorff dimension) and `sard_equidim_general`, for analytic
  maps.
- **Observed-pattern bounds** --- at most \(d!\), at most \(N\), and at most the minimal
  period (`card_observedPatterns_le_factorial`, `card_observedPatterns_le_length`,
  `card_observedPatterns_le_period`).
- **Coincidence length** --- `coincidenceLength` and `exists_separatingWindow_iff`: on a
  finite state space, some window separates orbits iff every distinct pair is eventually
  distinguished.
- **Determinant lemmas** --- `det_fderiv_eq_zero_of_not_surjective` and
  `ContinuousLinearMap.surjective_iff_det_ne_zero`.
- **Period bridge** --- `separatesOrbits_of_injective` and window distinctness from minimal
  periods.
- **Embedding chain** --- `smoothDelayMap_isClosedEmbedding` and
  `smoothDelayMapRangeHomeomorph`.
- **Initial results** --- `delayEmbedding`, `SeparatesOrbits`,
  `delayEmbedding_injective_iff_separatesOrbits`, `ordinalPattern` with existence,
  uniqueness and surjectivity, and `ordinalDelayMap` with invariance under strictly
  increasing transformations.
