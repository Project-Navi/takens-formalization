# Measured Data

Delay-coordinate vectors and ordinal patterns are routinely built from measured time
series. This page states which theorems proved here concern those constructions, and what
they do not establish.

All results below are exact statements about mathematical models. No theorem here verifies
that a particular sensor, data set, neural network or residual stream satisfies their
hypotheses, and none addresses noise, finite precision or statistical estimation.

## Delay vectors

- **Exact reconstruction on a model.** A delay map is injective iff the observation
  separates orbits at that window (`delayEmbedding_injective_iff_separatesOrbits`). An
  injective delay map identifies the state space with its delay image and transports the
  dynamics there by conjugacy (`reconstructedDynamics_eq_conj`). For compact state spaces with
  continuous dynamics and observation, that identification is a homeomorphism onto the image
  (`delayHomeomorph`). The reconstructed dynamics is invertible only under the corresponding
  invertibility condition on the original dynamics.
- **Window length on a finite model.** When a finite separating window exists, the least one
  is the separating horizon and uses at most \(N - 1\) observations on \(N \ge 1\) states
  (`separatingHorizon_le_card_sub_one`); some pairs of states may never be distinguished, and
  then no window separates. The horizon can be computed exactly from exact finite data
  (`horizonSearch_eq_separating_iff`). A finite sample of a continuous system is not a finite
  state space.
- **Smooth models.** For a compact manifold of dimension \(d\) and an injective \(C^2\) map
  with injective differentials satisfying the periodic-point conditions (countably many points
  of period at most \(4d\), observability at points of period at most \(2d\)), the
  observations giving a \(C^2\) embedding with \(2d + 1\) delays form an open dense set in the
  \(C^2\) topology (`isOpen_and_dense_setOf_isContMDiffEmbedding_delayEmbedding`). This does
  not say that a given observation works, nor that a given map satisfies the conditions.
  Takens' theorem for generic pairs of a \(C^2\) diffeomorphism and a \(C^2\) observation
  (`isOpen_and_dense_setOf_isContMDiffEmbedding_delayEmbedding_pair`) says that good pairs are
  open and dense; it does not certify a particular pair either.

## Ordinal patterns and permutation entropy

- **Invariance.** Ordinal codes and pattern entropy are unchanged by strictly increasing
  transformations of the observation, and relabeled (entropy unchanged on tie-free
  segments) by strictly decreasing ones (`ordinalDelayMap_comp_strictMono`,
  `patternEntropy_comp_strictAnti`). Monotone but not strictly monotone transformations
  can create ties: tied windows leave the tie-free `ordinalDelayMap`, while the empirical
  statistics (`observedPatterns`, `patternEntropy`) still assign a stable-sort code, with no
  general invariance guarantee for such a transformation.
- **Bounds.** For \(N > 0\), the empirical pattern entropy of \(N\) windows of length \(d\)
  is at most \(\log \min(d!, N)\), and at most the log of the minimal period on a periodic orbit
  (`patternEntropy_le_log_min`, `patternEntropy_le_log_min_period`).
- **Compression, not reconstruction.** An ordinal code takes at most \(d!\) values, so it
  cannot distinguish more than \(d!\) states (`not_injective_ordinalDelayMap_of_factorial_lt`).
  A quantity can be computed from the code iff it is constant on the code's fibers
  (`exists_factor_iff`); whether a quantity of interest has that property is a separate,
  target-specific question.

The relation between empirical pattern entropy and topological or metric entropy of the
underlying dynamics is not formalized here.
