[![Lean CI](https://github.com/Project-Navi/takens-formalization/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/Project-Navi/takens-formalization/actions/workflows/lean_action_ci.yml)
[![Docs](https://github.com/Project-Navi/takens-formalization/actions/workflows/docs.yml/badge.svg)](https://github.com/Project-Navi/takens-formalization/actions/workflows/docs.yml)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-orange)](LICENSE)

# Delay embeddings in Lean 4

A Lean 4 and Mathlib formalization of delay-coordinate reconstruction
`x ↦ (h x, h (T x), …, h (T^(k-1) x))`, from finite state spaces to compact manifolds.

## What is proved

- **Takens' theorem for generic pairs.** On a compact smooth `d`-manifold `M` without
  boundary, the pairs `(T, h)` of a `C²` diffeomorphism and a `C²` observation whose delay
  map with `2d + 1` coordinates is a `C²` embedding form an open dense subset of
  `Diff²(M) × C²(M, ℝ)`
  (`isOpen_and_dense_setOf_isContMDiffEmbedding_delayEmbedding_pair`). Each factor carries
  the `C²` topology defined through chart derivatives on compact windows, which on a compact
  manifold is the Whitney topology.
- **Kupka–Smale density.** The `C²` diffeomorphisms whose points of period at most `4d` are
  nondegenerate, with observable differentials, are dense (`dense_setOf_goodUpTo`).
- **Takens' theorem for a fixed map.** For an injective `C²` map with injective
  differentials, countably many points of period at most `4d` and an observability condition
  at points of period at most `2d`, the good observations are open and dense
  (`isOpen_and_dense_setOf_isContMDiffEmbedding_delayEmbedding`), and Lebesgue-almost every
  member of one finite family of perturbations is good.
- **Sard's theorem at finite regularity.** For `f : E → F` of class `C^r` with
  `r ≥ dim E - dim F + 1`, the critical values are Haar-null (`sard`), via a port of
  Moreira's theorem.
- **Finite state spaces and ordinal codes.** The exact separating horizon, the sharp bound
  `N - 1` (attained), a sound and complete decision procedure, reconstruction of the dynamics
  on the image; ordinal patterns, their invariances, pattern-count and entropy bounds.

The Sauer–Yorke–Casdagli extension to fractal sets and prevalence is not formalized here.

## Verification

Every selected declaration depends only on `propext`, `Classical.choice` and `Quot.sound`;
there are no `sorry`s, no custom axioms and no assumption classes. CI builds every module
with warnings as errors and runs the linter, the axiom records, a documented-name check and
a fresh kernel replay (see `AGENTS.md`).

```bash
lake exe cache get && make build lint verify
```

Documentation: <https://project-navi.github.io/takens-formalization/>.

## Credit

Mathematics after Takens (1981), Bandt and Pompe (2002), Sauer, Yorke and Casdagli (1991)
and Moreira (2001). `TakensFormal/ForMathlib/SardMoreira/` ports Yury Kudryashov's Lean
proof of Moreira's theorem (`urkud/SardMoreira`, Apache 2.0). Formalization by Nelson
Spence with AI assistance. Licensed under [Apache 2.0](LICENSE).
