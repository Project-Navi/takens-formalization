[![CI](https://github.com/Project-Navi/takens-formalization/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/Project-Navi/takens-formalization/actions/workflows/lean_action_ci.yml)
![Lean v4.28.0](https://img.shields.io/badge/Lean-v4.28.0-blue)
![Mathlib](https://img.shields.io/badge/Mathlib-dep-blue)
![sorry-free](https://img.shields.io/badge/sorry--free-%E2%9C%93-brightgreen)
![no custom axioms](https://img.shields.io/badge/custom%20axioms-0-brightgreen)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-orange)](LICENSE)

# Delay Embedding Theory — Lean 4 Formalization

Formal verification of delay embedding characterization, ordinal pattern
compression, and the topological embedding chain for compact dynamical systems.

## Mathematical background

The Takens delay embedding theorem (1981) states that for a generic observation
function on a compact manifold, the delay coordinate map
`x ↦ (α(x), α(f(x)), …, α(f^{2d}(x)))` is a topological embedding into
`ℝ^{2d+1}`. This is the theoretical foundation for reconstructing dynamical
system attractors from scalar time series data.

Route B formalizes the combinatorial core: for finite dynamical systems, the
delay embedding is injective if and only if the observation separates orbit
pairs within the observation window (`SeparatesOrbits`). Route A addresses
the classical smooth setting, where the embedding chain (compact + injective →
closed embedding) is proved axiom-free, and genericity requires Sard's theorem
(not yet in Mathlib).

## What is verified

**Route B (discrete, 24 declarations):** The delay coordinate map
`x ↦ (α(x), α(f(x)), …, α(f^[k-1](x)))` is injective if and only if
the observation `α` separates all pairs of states whose first `k` iterates
under `f` coincide (`SeparatesOrbits`). For non-injective observations on
finite types, a separating window exists iff orbits eventually differ under
`α` — the minimum window equals the maximum coincidence length over all
distinct pairs. The ordinal pattern of the delay window is invariant under
strictly monotone transformations, and the number of observed patterns along
an orbit is bounded by `min(d!, N, period)`.

**Route A (smooth, 18 declarations):** For a compact topological space,
a continuous injective map to a Hausdorff space is a closed embedding, and
the range factorization is a homeomorphism. Applied to the delay coordinate
map with continuous dynamics and observation. `SmoothTakens` is axiom-free
(does not import `SardInfra`). `SardInfra` proves Sard's theorem for the
equidimensional case (via the Jacobian area formula) and the low-dimensional
case (via Hausdorff dimension bounds). The high-dimensional Morse–Sard case
is deferred to a typeclass at gate 3.

### Proof spine

| Step | Declaration | File |
|------|-------------|------|
| Ordinal pattern predicate | `IsOrdinalPatternOf` | `OrdinalPattern` |
| Sorting permutation | `ordinalPattern` | `OrdinalPattern` |
| Existence + uniqueness | `ordinalPattern_exists_unique` | `OrdinalPattern` |
| Monotone invariance | `isOrdinalPatternOf_comp_strictMono` | `OrdinalPattern` |
| Every perm realizable | `ordinalPattern_surjective` | `OrdinalPattern` |
| Delay coordinate map | `delayEmbedding` | `DelayWindow` |
| Orbit separation | `SeparatesOrbits` | `DelayWindow` |
| **Headline iff** | **`delayEmbedding_injective_iff_separatesOrbits`** | **`DelayWindow`** |
| First-disagreement | `coincidenceLength` | `DelayWindow` |
| Finite existence | `exists_separatingWindow_iff` | `DelayWindow` |
| Continuity | `delayEmbedding_continuous` | `DelayWindow` |
| Image card bounds | `delayEmbedding_image_card_le/of_injective` | `DelayWindow` |
| Trivial separation | `separatesOrbits_of_injective` | `IteratePeriod` |
| Tie-free windows | `windowDistinct_of_injective_of_le_minimalPeriod` | `IteratePeriod` |
| Collision → periodicity | `isPeriodicPt_of_injective_iterate_eq` | `IteratePeriod` |
| Orbit distinctness | `windowDistinct_of_injective_orbit` | `IteratePeriod` |
| Ordinal delay map | `ordinalDelayMap` | `OrdinalTakens` |
| PE robustness | `ordinalDelayMap_monotone_invariant` | `OrdinalTakens` |
| Order characterization | `ordinalDelayMap_eq_of_order_eq` | `OrdinalTakens` |
| Observed patterns | `observedPatterns` | `OrdinalTakens` |
| Bound ≤ d! | `card_observedPatterns_le_factorial` | `OrdinalTakens` |
| Bound ≤ N | `card_observedPatterns_le_length` | `OrdinalTakens` |
| Bound ≤ period | `card_observedPatterns_le_period` | `OrdinalTakens` |
| Critical set | `criticalSet` / `criticalValues` | `SardInfra` |
| Surjective ↔ det ≠ 0 | `ContinuousLinearMap.surjective_iff_det_ne_zero` | `SardInfra` |
| Det vanishes at critical | `det_fderiv_eq_zero_of_not_surjective` | `SardInfra` |
| Critical = det-zero | `criticalSet_eq_det_zero` | `SardInfra` |
| Critical set closed | `isClosed_criticalSet_of_contDiff` | `SardInfra` |
| **Sard equidim** | **`sard_equidim`** | **`SardInfra`** |
| **Sard low-dim** | **`sard_low_dim`** | **`SardInfra`** |
| **Sard equidim general** | **`sard_equidim_general`** | **`SardInfra`** |
| Smooth delay map | `smoothDelayMap` | `SmoothTakens` |
| Continuity | `smoothDelayMap_continuous` | `SmoothTakens` |
| **Closed embedding** | **`smoothDelayMap_isClosedEmbedding`** | **`SmoothTakens`** |
| Embedding | `smoothDelayMap_isEmbedding` | `SmoothTakens` |
| Homeomorphism | `smoothDelayMap_rangeHomeomorph` | `SmoothTakens` |

## Axiom boundary

**Zero custom axioms.** All 42 declarations depend only on
`[propext, Classical.choice, Quot.sound]` with no `sorryAx`.
The `#print axioms` dashboard in `Verify.lean` confirms this.

`SardInfra.lean` proves Sard's theorem for the equidimensional and
low-dimensional cases. The `SardInfra` typeclass (axiomizing
`sard_of_finrank_gt` for the high-dimensional Morse–Sard case) is deferred
to gate 3. `SmoothTakens.lean` does not import `SardInfra` — its
embedding chain is axiom-free.

## File structure

| File | Role | Status |
|------|------|--------|
| `OrdinalPattern.lean` | Bandt-Pompe ordinal pattern map (upstream candidate) | Proved |
| `DelayWindow.lean` | Delay embedding + SeparatesOrbits + coincidenceLength | Proved |
| `IteratePeriod.lean` | Period bridge lemmas | Proved |
| `TakensDiscrete.lean` | Future finite-horizon corollaries | Skeleton |
| `OrdinalTakens.lean` | Ordinal delay compression + observedPatterns | Proved |
| `SardInfra.lean` | Sard equidim + low-dim; high-dim typeclass deferred | Proved (2 of 3 cases) |
| `SmoothTakens.lean` | Embedding chain: continuity → homeomorphism | Proved |
| `Verify.lean` | Axiom dashboard (diagnostic) | Active |

### Upstream candidates

| Declaration | File | Mathlib status |
|-------------|------|----------------|
| `ordinalPattern` + API | `OrdinalPattern` | No ordinal pattern map in Mathlib |
| `delayEmbedding` + characterization | `DelayWindow` | No `Dynamics.delayEmbedding` in Mathlib |

## Building

```bash
lake build --wfail                     # primary — warnings are errors
lake lint                              # Mathlib linter suite
lake build TakensFormal.Verify         # axiom dashboard (compilation check)
lake env lean TakensFormal/Verify.lean # display axiom output
```

Requires Lean 4.28.0 (via `lean-toolchain`) and Mathlib v4.28.0 (via `lakefile.toml`).

## Development process

**What the author did**: The formalization architecture — the dual-route
design, the rescope from trivial injective-α injectivity to honest orbit
separation characterization, the property-first ordinal pattern design,
the coincidence length theory for non-injective observations, and the
compression/quotient framing for ordinal delay maps — is the core
contribution. The underlying mathematics is from Takens (1981) and
Bandt-Pompe (2002).

**What AI tools did**: Claude Opus assisted with Lean 4 syntax, Mathlib API
navigation, and proof term synthesis. Aristotle (Harmonic) independently
proved leaf lemmas (existence/uniqueness, monotone invariance, period bounds,
embedding chain, Sard equidim/low-dim) and provided API reconnaissance that shaped
definition design. These roles are analogous to `omega`, `aesop`, and other
proof automation — the strategy is human, the term-level search is
machine-assisted.

**Verification**: The final arbiter is the Lean compiler:
```bash
lake build --wfail   # type-checks or it doesn't
```

## License

Copyright 2026 Nelson Spence. Licensed under [Apache 2.0](LICENSE).
