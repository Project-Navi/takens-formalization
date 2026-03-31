# Formal Backing for navi-SAD

This page maps the formalized theorems in this project to the
[navi-SAD](https://project-navi.github.io/navi-SAD/) instrument pipeline. If you
use navi-SAD and want to understand what the formal guarantees actually say ---
and where they stop --- this is the page to read.

For the full theoretical context in navi-SAD's own documentation, see
[Takens Embedding](https://project-navi.github.io/navi-SAD/theory/takens-embedding/).

---

## Delay embedding and attractor reconstruction

navi-SAD treats per-head SAD trajectories as delay-coordinate embeddings: given a
time series of scalar observations, it reconstructs the dynamics by forming
vectors of consecutive observations with a fixed lag.

The formalized guarantee behind this is
`delayEmbedding_injective_iff_separatesOrbits` (in `DelayWindow.lean`). It says:
the delay embedding is injective --- meaning distinct dynamical states produce
distinct observation vectors --- if and only if the observation function separates
orbits of the given window length. "Separates orbits" means that for any two
distinct states, at least one of the first k iterates produces a different
observed value.

The companion theorem `exists_separatingWindow_iff` makes this operational for
finite systems: on a finite state space, a separating window length exists if and
only if every pair of distinct states eventually disagrees under observation. The
`coincidenceLength` definition gives the exact index of first disagreement for
each pair, and the separating window length is bounded by the maximum
coincidence length over all pairs.

**What this guarantees.** If the observation separates orbits at window length k,
the delay embedding at that window length is a faithful representation of the
dynamics --- no information is lost. Distinct states are always distinguishable.

**What this does not guarantee.** The discrete theory does not address noise,
finite precision, or continuous-time sampling. It also does not say how to *find*
a separating observation --- only that the embedding is injective when one is used.

---

## Ordinal patterns and permutation entropy

navi-SAD computes permutation entropy (PE) from ordinal patterns: the relative
ordering of values within each delay window, discarding magnitudes.

Two formalized results underpin this:

**Monotone invariance.** `isOrdinalPatternOf_comp_strictMono` (in
`OrdinalPattern.lean`) proves that applying any strictly monotone transformation
to the observation does not change the ordinal pattern. This is why PE is
well-defined regardless of the scale, offset, or any monotone nonlinearity in the
observation function. If two sensors measure the same quantity through different
monotone response curves, they produce the same ordinal patterns.

**Pattern-count bounds.** The number of distinct ordinal patterns observed along
an orbit is bounded in two ways (in `OrdinalTakens.lean`):

- `card_observedPatterns_le_factorial` --- at most k! patterns exist for window
  size k, since ordinal patterns are permutations of k elements.
- `card_observedPatterns_le_period` --- on a periodic orbit, the number of
  distinct patterns is at most the minimal period.

These bounds constrain the range of PE. The factorial bound is the theoretical
maximum (log of k! gives the maximum PE for window size k). The period bound is
tighter for periodic or nearly periodic dynamics, which is the regime where PE is
most informative as a complexity measure.

**What this guarantees.** PE is invariant under monotone observation transforms
and has known combinatorial bounds. The `ordinalDelayMap` (which composes the
delay embedding with ordinal pattern extraction) is a well-defined compression
of the delay window.

**What this does not guarantee.** The formalization does not address statistical
estimation of PE from finite samples, the relationship between PE and
topological/metric entropy, or the effect of ties in observed values (the
ordinal pattern is defined only for injective windows, via the `WindowDistinct`
subtype).

---

## Smooth embedding chain

The smooth-category version of the delay embedding theorem provides a different
kind of guarantee, relevant to the theoretical foundations rather than the
computational pipeline.

`smoothDelayMap_isClosedEmbedding` (in `SmoothTakens.lean`) proves: if the state
space is compact, the dynamics and observation are continuous, and the delay map
is injective, then the delay map is a closed embedding. The companion
`smoothDelayMap_rangeHomeomorph` strengthens this to a homeomorphism onto its
image --- the delay map is not just injective but topologically faithful.

This is the result that justifies calling the delay-coordinate reconstruction a
genuine embedding of the attractor, not merely an injective function. Compactness
+ injectivity + continuity is enough; no smoothness beyond continuity is needed
for the embedding conclusion.

Note: the compactness and continuity hypotheses of this theorem are not verified
for the LLM residual stream setting. This result provides theoretical motivation
rather than a direct operational guarantee for navi-SAD's pipeline.

**What this guarantees.** The topology of the attractor is preserved by the delay
embedding. Neighborhoods map to neighborhoods; connected components are preserved;
the reconstructed attractor is homeomorphic to the original.

**What this does not guarantee.** This is the topological embedding, not the full
smooth Takens theorem. The genericity result --- that the embedding works for
*generic* pairs of dynamics and observations, not just injective ones --- requires
Sard's theorem and parametric transversality, which are partially formalized
(equidimensional and low-dimensional Sard are proved) but not yet connected to
the embedding chain.

---

## What is in progress

The finite-horizon corollaries in `TakensDiscrete.lean` --- concrete window-length
bounds, decidability results for finite systems, and cardinality estimates --- are
currently a skeleton. These are the results most directly relevant to navi-SAD's
computational pipeline, where window length and pattern counts are concrete
parameters rather than existential statements.

See [Open Problems](../research/open-problems.md) (Tier 1) for the current state
and what filling in these corollaries involves.

The genericity theorem --- which would say that the delay embedding works for
*almost every* observation, not just injective ones --- is a research-grade open
problem. See [Open Problems](../research/open-problems.md) (Tier 3) and the
[Roadmap](../research/roadmap.md) for the path forward.
