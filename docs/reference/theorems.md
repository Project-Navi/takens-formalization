# Theorem Catalog

The declarations selected in
[`Verify.lean`](https://github.com/Project-Navi/takens-formalization/blob/main/TakensFormal/Verify.lean),
by module. CI checks that each depends only on `propext`, `Classical.choice` and
`Quot.sound` (see the [Axiom Dashboard](axiom-dashboard.md)). A clean axiom record does not
discharge a theorem's hypotheses: they are part of the statement, summarized below and
given in full in the source.

Notation: \(\Phi_k(x) = (\alpha(x), \alpha(fx), \dots, \alpha(f^{k-1}x))\) is the delay
map (`delayEmbedding f α k`); \(d = \dim M\) on a manifold \(M\).

---

## Finite and discrete delay maps

### OrdinalPattern

| Declaration | Statement |
|---|---|
| `IsOrdinalPatternOf` | \(\sigma\) is the ordinal pattern of \(v : \mathrm{Fin}\,d \to \mathbb{R}\) if \(v \circ \sigma\) is strictly increasing |
| `ordinalPattern` | The ordinal pattern of a tie-free \(v\) |
| `ordinalPattern_exists_unique` | A tie-free \(v\) has exactly one ordinal pattern |
| `isOrdinalPatternOf_comp_strictMono` | A strictly increasing \(g\) preserves ordinal patterns |
| `ordinalPattern_surjective` | Every permutation is the pattern of some tie-free vector |
| `ordinalPattern_eq_tuple_sort` | The ordinal pattern is Mathlib's `Tuple.sort` |
| `ordinalPattern_eq_iff` | Two tie-free vectors have the same pattern iff they induce the same strict order |
| `ordinalPattern_comp_strictMono` | Pattern of \(g \circ v\) equals pattern of \(v\) for strictly increasing \(g\) |
| `ordinalPattern_comp_strictAnti` | For strictly decreasing \(g\), the pattern of \(g \circ v\) is \(\sigma \circ \mathrm{rev}\) |
| `Tuple.sort_comp_strictMono` | The stable sort is invariant under strictly increasing \(g\), ties included |
| `card_equiv_perm_fin` | There are \(d!\) ordinal patterns of order \(d\) |

### DelayWindow

| Declaration | Statement |
|---|---|
| `delayEmbedding` | The delay map \(\Phi_k\) |
| `SeparatesOrbits` | \(\alpha\) separates \(f\)-orbits at window \(k\): equal windows force equal states |
| `WindowDistinct` | The window at \(x\) has no ties |
| `delayEmbedding_injective_iff_separatesOrbits` | \(\Phi_k\) is injective iff \(\alpha\) separates orbits at window \(k\) |
| `separatesOrbits_of_le` | Separation at \(m\) implies separation at every \(n \ge m\) |
| `delayEmbedding_continuous` | \(\Phi_k\) is continuous for continuous \(f\), \(\alpha\) |
| `delayEmbedding_iterate_apply` | A sampling lag \(q\) is the delay map of \(f^q\) |
| `delayEmbedding_succ_eq_iff` | Windows of length \(k+1\) agree iff the first values and the next windows of length \(k\) agree |
| `coincidenceLength` | First index where the observed orbits of \(x\), \(y\) differ, in \(\mathbb{N}_\infty\) |
| `natCast_le_coincidenceLength_iff` | \(n \le c(x,y)\) iff the observations agree before \(n\) |
| `delayEmbedding_eq_iff_le_coincidenceLength` | \(\Phi_k(x) = \Phi_k(y)\) iff \(k \le c(x,y)\) |
| `coincidenceLength_eq_top_iff` | \(c(x,y) = \infty\) iff the observations agree at every time |
| `coincidenceLength_eq_natCast_iff` | \(c(x,y) = n\) iff agreement before \(n\) and disagreement at \(n\) |
| `coincidenceLength_comm` | \(c\) is symmetric |
| `coincidenceLength_self` | \(c(x,x) = \infty\) |
| `coincidenceLength_eq_zero_iff` | \(c(x,y) = 0\) iff \(\alpha(x) \ne \alpha(y)\) |
| `coincidenceLength_of_ne` | One-step recursion, first values differ |
| `coincidenceLength_of_eq` | One-step recursion: \(c(x,y) = c(fx, fy) + 1\) when \(\alpha(x) = \alpha(y)\) |
| `separatesOrbits_iff_forall_coincidenceLength_lt` | Separation at \(k\) iff \(c(x,y) < k\) for all \(x \ne y\) |
| `separatingHorizon` | \(\sup_{x \ne y} (c(x,y) + 1)\) in \(\mathbb{N}_\infty\) |
| `separatesOrbits_iff_separatingHorizon_le` | Separation at \(k\) iff the horizon is at most \(k\) |
| `exists_separatesOrbits_iff_separatingHorizon_ne_top` | Some window separates iff the horizon is finite |
| `isLeast_separatingHorizon` | A finite horizon is the least separating window |
| `separatingHorizon_eq_zero_iff` | The horizon is \(0\) iff there are no two distinct states |
| `separatingHorizon_eq_top_of_forall` | A never-distinguished pair forces an infinite horizon |
| `exists_separatingHorizon_eq` | On a finite space the horizon is attained by a pair |
| `separatingHorizon_eq_top_iff` | On a finite space the horizon is infinite iff some pair is never distinguished |
| `exists_separatingWindow_iff` | On a finite space some window separates iff every distinct pair is eventually distinguished |
| `delayEmbedding_image_card_le` | At most \(\lvert X\rvert\) distinct windows |
| `delayEmbedding_image_card_of_injective` | Exactly \(\lvert X\rvert\) windows when \(\Phi_k\) is injective |

### IteratePeriod

| Declaration | Statement |
|---|---|
| `separatesOrbits_of_injective` | An injective observation separates orbits at every \(k \ge 1\) |
| `windowDistinct_of_injective_of_le_minimalPeriod` | Injective \(\alpha\) and \(k \le\) minimal period give a tie-free window |
| `isPeriodicPt_of_injective_iterate_eq` | For injective \(f\), a repeated iterate makes \(x\) periodic |
| `windowDistinct_of_injective_orbit` | Injective \(\alpha\) and a non-repeating orbit segment give a tie-free window |

### TakensDiscrete

| Declaration | Statement |
|---|---|
| `forall_iterate_eq_of_delayEmbedding_eq` | On \(N\) states, equal windows of length \(N-1\) give equal observations at all times |
| `coincidenceLength_lt_card_sub_one` | A finite coincidence length on \(N\) states is below \(N-1\) |
| `separatingHorizon_le_card_sub_one` | A finite horizon on \(N\) states is at most \(N-1\) |
| `separatesOrbits_card_sub_one_iff` | Window \(N-1\) separates iff some window does |
| `countdown` | The chain \(i \mapsto i-1\) on \(\mathrm{Fin}\,N\), \(0\) fixed |
| `countdownObs` | The indicator of state \(0\) |
| `separatingHorizon_countdown` | The countdown chain needs exactly \(N-1\) coordinates: the bound is sharp |
| `HorizonResult` | Result type of the horizon search |
| `horizonSearch` | Exact search for the least separating window on \(\mathrm{Fin}\,n\) |
| `horizonSearch_separating` | A `separating k` answer is the exact horizon |
| `horizonSearch_indistinguishable` | An `indistinguishable x y` answer is a distinct pair never distinguished |
| `horizonSearch_eq_separating_iff` | The search returns `separating k` iff the horizon is \(k\) |
| `exists_horizonSearch_eq_indistinguishable_iff` | The search returns a pair iff the horizon is infinite |

### Reconstruction

| Declaration | Statement |
|---|---|
| `delayDecoder` | The inverse of an injective delay map on its image |
| `delayDecoder_delayEmbedding` | Decoding a window returns the state |
| `delayEmbedding_delayDecoder` | Encoding a decoded window returns the window |
| `reconstructedDynamics` | \(\Phi_k \circ f \circ \Phi_k^{-1}\) on the image |
| `reconstructedDynamics_delayEmbedding` | It maps the window of \(x\) to the window of \(fx\) |
| `reconstructedDynamics_iterate_delayEmbedding` | The same for iterates |
| `reconstructedDynamics_apply_of_lt` | Shift formula: only the last coordinate is new |
| `reconstructedDynamics_bijective` | Bijective for bijective \(f\) |
| `delayHomeomorph` | For compact \(X\), an injective delay map is a homeomorphism onto its image |
| `continuous_delayDecoder` | The decoder is continuous (compact \(X\)) |
| `reconstructedDynamics_eq_conj` | The reconstructed dynamics is conjugate to \(f\) by the homeomorphism |
| `continuous_reconstructedDynamics` | The reconstructed dynamics is continuous (compact \(X\)) |

---

## Ordinal codes

### OrdinalTakens

| Declaration | Statement |
|---|---|
| `ordinalDelayMap` | The ordinal pattern of the window, on tie-free states |
| `ordinalDelayMap_monotone_invariant` | Invariant under strictly increasing transformations of \(\alpha\) |
| `windowDistinct_comp` | An injective transformation keeps windows tie-free |
| `ordinalDelayMap_comp_strictMono` | Invariance under strictly increasing \(g\) |
| `ordinalDelayMap_comp_strictAnti` | Relabeling \(\sigma \mapsto \sigma \circ \mathrm{rev}\) under strictly decreasing \(g\) |
| `ordinalDelayMap_eq_iff` | Equal codes iff the windows induce the same strict order |
| `ordinalDelayMap_eq_of_order_eq` | Same strict order gives the same code |
| `observedPatterns` | The patterns seen along \(N\) windows of an orbit |
| `observedPatterns_comp_strictMono` | Invariant under strictly increasing \(g\), ties included |
| `observedPatterns_comp_strictAnti` | Relabeled under strictly decreasing \(g\) on tie-free segments |
| `coe_observedPatterns_eq_ordinalDelayMap` | On tie-free segments, the observed patterns are the codes along the orbit |
| `card_observedPatterns_le_factorial` | At most \(d!\) observed patterns |
| `card_observedPatterns_le_length` | At most \(N\) |
| `card_observedPatterns_le_period` | At most the minimal period on a periodic orbit |

### OrdinalEntropy

| Declaration | Statement |
|---|---|
| `patternCount` | Number of windows with a given pattern |
| `patternFreq` | Empirical frequency of a pattern |
| `patternEntropy` | Shannon entropy of the empirical pattern distribution |
| `sum_patternCount` | Counts add up to \(N\) |
| `sum_patternFreq` | Frequencies add up to \(1\) for \(N > 0\) |
| `patternCount_pos_iff` | Positive count iff the pattern is observed |
| `patternEntropy_nonneg` | The entropy is nonnegative |
| `patternEntropy_le_log_card` | At most the log of the number of observed patterns |
| `patternEntropy_le_log_min` | At most \(\log \min(d!, N)\) |
| `patternEntropy_le_log_min_period` | Also at most the log of the minimal period on periodic orbits |
| `patternEntropy_comp_strictMono` | Invariant under strictly increasing \(g\) |
| `patternCount_comp_strictAnti` | Counts relabel under strictly decreasing \(g\) on tie-free segments |
| `patternEntropy_comp_strictAnti` | Entropy is invariant under strictly decreasing \(g\) on tie-free segments |
| `patternEntropy_zero_length` | No windows, zero entropy |
| `patternEntropy_eq_zero_of_le_one` | Windows of length at most \(1\) carry no entropy |

### OrdinalQuotient

| Declaration | Statement |
|---|---|
| `ordinalSetoid` | Two tie-free states are equivalent if they have the same code |
| `ordinalSetoid_iff` | Equivalence is equality of the strict orders of the windows |
| `ordinalQuotientEquivRange` | The quotient is in bijection with the codes that occur |
| `exists_factor_iff` | A quantity factors through the code iff it is constant on code fibers |
| `factor_unique` | The factor is unique on the codes that occur |
| `exists_ordinalDynamics_iff` | Codes evolve by a map on codes iff equal codes have equal next codes |
| `not_injective_ordinalDelayMap_of_factorial_lt` | The code is not injective on more than \(k!\) tie-free states |
| `not_injective_ordinalDelayMap_of_infinite` | Nor on infinitely many |

---

## Sard's theorem

### SardInfra

| Declaration | Statement |
|---|---|
| `criticalSet` | Points where the derivative is not surjective |
| `criticalValues` | Image of the critical set |
| `det_fderiv_eq_zero_of_not_surjective` | A non-surjective endomorphism has determinant \(0\) |
| `ContinuousLinearMap.surjective_iff_det_ne_zero` | Surjective iff nonzero determinant |
| `criticalSet_eq_det_zero` | The critical set of \(f : E \to E\) is the zero set of the Jacobian |
| `isClosed_criticalSet` | Closed critical set for \(C^1\) maps |
| `isClosed_criticalSet_of_contDiff` | The same for analytic maps (original statement) |
| `sard_equidim_of_contDiff` | \(C^1\), \(E \to E\): critical values are Haar-null (area formula) |
| `sard_equidim` | The same for analytic maps (original statement) |
| `addHaar_image_eq_zero_of_differentiableOn_of_finrank_lt` | A differentiable image of a lower-dimensional set is Haar-null |
| `sard_low_dim_of_contDiff` | \(C^1\), \(\dim E < \dim F\): critical values are Haar-null |
| `sard_low_dim` | The same for analytic maps (original statement) |
| `exists_continuousLinearEquiv_of_finrank_eq` | Equal dimensions give a continuous linear equivalence |
| `criticalSet_comp_equiv` | Post-composition with an equivalence keeps the critical set |
| `ContinuousLinearEquiv.symm_preimage_eq_image` | \(e^{-1}\)-preimage equals \(e\)-image |
| `map_continuousLinearEquiv_isAddHaarMeasure` | Transport of an additive Haar measure |
| `sard_equidim_general_of_contDiff` | \(C^1\), \(\dim E = \dim F\): critical values are Haar-null |
| `sard_equidim_general` | The same for analytic maps (original statement) |

### Sard (with the ported Moreira theorem)

| Declaration | Statement |
|---|---|
| `hausdorffMeasure_sardMoreiraBound_image_null_of_finrank_le` | Moreira's theorem: rank-\(\le p\) points of a \(C^{k+(\alpha)}\) map have \(\mathcal{H}^{s}\)-null image, \(s = p + (n-p)/(k+\alpha)\) (ported) |
| `sardMoreiraBound` | The exponent \(p + (n-p)/(k+\alpha)\) (ported) |
| `coe_sardMoreiraBound_sub_add_one` | For rank \(m-1\), order \(n-m+1\), \(\alpha = 0\) the exponent is \(m\) |
| `criticalSet_eq_empty_of_finrank_eq_zero` | Maps into a zero-dimensional space have no critical points |
| `addHaar_image_inter_criticalSet_eq_zero` | Local form: \(C^r\) at every point of \(s\) gives Haar-null critical values on \(s\) |
| `addHaar_image_inter_criticalSet_eq_zero_of_contDiffOn` | Open-set form |
| `sard` | **Sard's theorem:** \(C^r\) with \(r \ge \dim E - \dim F + 1\) gives Haar-null critical values |

---

## Genericity in finite-dimensional families

### Avoidance

| Declaration | Statement |
|---|---|
| `exists_lipschitzOnWith_levelSet_subset_image` | Near a submersion point, a level set is a Lipschitz image of a piece of the kernel |
| `addHaar_image_levelSet_eq_zero` | Projections of such level sets of too small dimension are Haar-null |
| `range_eq_top_of_comp_inl` | A derivative onto in the first factor is onto |
| `ae_forall_ne_of_hasStrictFDerivAt` | Parametric avoidance: for almost every parameter, \(\Phi(a, \cdot)\) misses \(c\) on \(U\) when \(\dim Z < \dim Y\) |

### GenericFamily

| Declaration | Statement |
|---|---|
| `ae_forall_add_apply_ne` | An affine family \(G_0 + L\,a\) with onto \(L\) misses a value on a lower-dimensional set for a.e. \(a\) |
| `ae_forall_injective_fderiv_add_apply` | Generic immersion in an affine family when \(2\dim X \le \dim Y\) |
| `ae_forall_add_apply_ne_add_apply` | Generic separation of two affine families when \(\dim X_1 + \dim X_2 < \dim Y\) |
| `ae_forall_injective_fderiv_add_sum` | Generic immersion for \(\Psi_0 + \sum_i a_i \Psi_i\) under a span condition |
| `ae_forall_add_sum_ne_add_sum` | Generic separation for finite families under a span condition |

---

## Smooth delay maps

### SmoothTakens

| Declaration | Statement |
|---|---|
| `smoothDelayMap` | The real-valued delay map (compatibility name for `delayEmbedding`) |
| `smoothDelayMap_continuous` | Continuous for continuous data |
| `smoothDelayMap_isClosedEmbedding` | Compact domain and injective: a closed embedding |
| `smoothDelayMap_isEmbedding` | Compact domain and injective: an embedding |
| `smoothDelayMapRangeHomeomorph` | Homeomorphism onto the image |
| `smoothDelayMap_eq_delayEmbedding` | It is `delayEmbedding` |

### SmoothDelay

| Declaration | Statement |
|---|---|
| `IsContMDiffEmbedding` | A \(C^r\) map with injective differentials that is a topological embedding |
| `IsContMDiffEmbedding.of_le` | A \(C^r\) embedding is a \(C^s\) embedding for \(s \le r\) |
| `IsContMDiffEmbedding.isDiffImmersionAt` | Its differential has a continuous left inverse |
| `isContMDiffEmbedding_of_injective` | On a compact manifold an injective \(C^r\) immersion is a \(C^r\) embedding |
| `contMDiff_delayEmbedding` | \(C^n\) dynamics and observation give a \(C^n\) delay map |
| `mfderiv_iterate_succ_apply` | Chain rule for iterates |
| `delayCovector` | The covector \(Dh_{T^i x} \circ D(T^i)_x\) |
| `delayCovector_eq_mvfderiv` | It is the differential of \(h \circ T^i\) |
| `mfderiv_delayEmbedding_apply` | The \(i\)-th coordinate of the differential is the \(i\)-th delayed covector |
| `injective_mfderiv_delayEmbedding_iff` | Immersion at \(x\) iff no nonzero vector is killed by all delayed covectors |
| `injective_mfderiv_delayEmbedding_iff_span` | Immersion at \(x\) iff the delayed covectors span the cotangent space |
| `finrank_le_of_injective_mfderiv_delayEmbedding` | An immersion needs at least \(d\) coordinates |
| `not_injective_mfderiv_delayEmbedding_id` | For \(T = \mathrm{id}\) and \(d \ge 2\), no observation gives an immersion |
| `isContMDiffEmbedding_delayEmbedding` | Compact, injective and immersive: a \(C^r\) embedding |

### DelayPerturbation

| Declaration | Statement |
|---|---|
| `perturbObservation` | The observation \(h + \sum_i a_i \varphi_i\) |
| `delayEmbedding_perturbObservation` | Its delay map is affine in \(a\) |
| `contMDiff_perturbObservation` | It is \(C^n\) for \(C^n\) data |
| `ae_forall_injective_mfderiv_delayEmbedding_perturb` | If the differentials of the \(\varphi_i\)-delay maps span \(\mathbb{R}^k\) along every nonzero vector and \(2d \le k\), a.e. perturbation is an immersion |
| `ae_forall_delayEmbedding_perturb_ne` | If differences of \(\varphi_i\)-delay vectors span \(\mathbb{R}^k\) on a set of pairs and \(2d < k\), a.e. perturbation separates those pairs |
| `ae_isContMDiffEmbedding_delayEmbedding_perturb` | Both span conditions everywhere on a compact manifold: a.e. perturbation is a \(C^2\) embedding |
| `exists_isContMDiffEmbedding_delayEmbedding_perturb` | Such perturbations exist with \(\lVert a \rVert < \varepsilon\) |

### DelaySpan

| Declaration | Statement |
|---|---|
| `InterpolatesValues` | Any values at \(n \le N\) distinct points are attained by a combination of the family |
| `InterpolatesDerivatives` | Any directional derivatives at \(n \le N\) distinct points are attained |
| `telescope_sub` | Explicit solution of \(v_j - v_{j+m} = c_j\) |
| `surjective_sum_smul_sub_delayEmbedding` | Separation span condition for injective \(T\) without periodic points of period \(\le 2k-2\) |
| `surjective_sum_smul_mvfderiv_delayEmbedding` | Immersion span condition when \(x, \dots, T^{k-1}x\) are distinct and \(DT\) is injective |
| `ae_isContMDiffEmbedding_delayEmbedding_perturb_of_interpolates` | Fixed \(T\) without periodic points of period \(\le 4d\): a.e. perturbation in an interpolating family has a \(C^2\) delay embedding with \(2d+1\) coordinates |

### InterpolatingFamily

| Declaration | Statement |
|---|---|
| `momentFunctional` | \(q \mapsto \sum_r t^r q_r\) in the coordinates of a basis |
| `exists_forall_momentFunctional_ne_zero` | Among \(L > \lvert V\rvert D\) moment functionals one vanishes on no vector of \(V\) |
| `momentFamily` | The functions \(x \mapsto (\ell_l(e(x)))^s\) |
| `interpolatesValues_momentFamily` | For injective \(e\), the family interpolates values at \(N\) points |
| `interpolatesDerivatives_momentFamily` | For an injective \(C^1\) immersion \(e\), it interpolates derivatives at \(N\) points |
| `ae_isContMDiffEmbedding_delayEmbedding_momentFamily` | Fixed-map theorem with this explicit family |
| `exists_family_forall_ae_isContMDiffEmbedding_delayEmbedding` | On a compact smooth manifold, one finite smooth family works for every injective \(C^2\) map with injective differentials and no periodic points of period \(\le 4d\), and every \(C^2\) observation |
| `exists_family_forall_exists_isContMDiffEmbedding_delayEmbedding` | The same with coefficient vectors of arbitrarily small norm |

### CircleDelay

| Declaration | Statement |
|---|---|
| `quarterTurn` | \(z \mapsto iz\) on the unit circle |
| `firstCoord` | \(z \mapsto \operatorname{Re} z\) |
| `not_injective_firstCoord` | The observation alone does not determine the state |
| `delayEmbedding_quarterTurn_injective_iff` | The delay map is injective iff \(k \ge 2\) |
| `injective_mfderiv_delayEmbedding_quarterTurn` | It is an immersion for \(k \ge 2\) |
| `isContMDiffEmbedding_delayEmbedding_quarterTurn_iff` | A \(C^r\) embedding iff \(k \ge 2\) |
| `isContMDiffEmbedding_delayEmbedding_quarterTurn` | \(2 \cdot 1 + 1 = 3\) coordinates give a \(C^2\) embedding |
