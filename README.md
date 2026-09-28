[![Lean CI](https://github.com/Project-Navi/takens-formalization/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/Project-Navi/takens-formalization/actions/workflows/lean_action_ci.yml)
[![Docs](https://github.com/Project-Navi/takens-formalization/actions/workflows/docs.yml/badge.svg)](https://github.com/Project-Navi/takens-formalization/actions/workflows/docs.yml)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-orange)](LICENSE)

# Delay embeddings in Lean 4

A Lean 4 and Mathlib formalization of delay-coordinate reconstruction
`x ↦ (h x, h (T x), …, h (T^(k-1) x))`, from finite state spaces to compact manifolds.

## What is proved

- **Takens' theorem for a fixed map, in the `C²` topology.** On a compact smooth
  `d`-manifold, let `T` be an injective `C²` map with injective differentials whose points of
  period at most `4d` are countably many, and which satisfies an observability condition at
  points of period at most `2d` (it holds when the differential of `T^p` there has distinct
  eigenvalues). Then the `C²` observations `h` whose delay map with `2d + 1` coordinates is a
  `C²` embedding form an open dense subset of `C²(M, ℝ)`
  (`isOpen_and_dense_setOf_isContMDiffEmbedding_delayEmbedding`). The topology is the weak
  `C²` topology defined through chart derivatives on compact windows, which on a compact
  manifold is the Whitney topology.
- **Almost every member of a finite family.** One finite family of smooth functions works for
  all such `T` and every `C²` observation `h`: the delay map of `h + ∑ q, a q • φ q` is a `C²`
  embedding for Lebesgue-almost every coefficient vector `a`
  (`exists_family_forall_ae_isContMDiffEmbedding_delayEmbedding_of_periodic`).
- **Stability of embeddings.** An injective immersion of a compact manifold stays one under
  `C¹`-small perturbations (`exists_forall_injective_of_near`).
- **Sard's theorem at finite regularity.** For `f : E → F` of class `C^r` with
  `r ≥ dim E - dim F + 1`, the critical values are Haar-null (`sard`), with local and
  open-set versions, via a port of Moreira's theorem.
- **Smooth delay maps.** Regularity, the differential and an immersion criterion; a compact
  injective immersion is a `C^r` embedding; the identity never immerses in dimension `≥ 2`.
- **Finite state spaces.** The exact separating horizon, the sharp bound `N - 1` (attained),
  a sound and complete decision procedure, and reconstruction of the dynamics on the image.
- **Ordinal codes.** Ordinal patterns, their behavior under strictly increasing and strictly
  decreasing transformations, pattern-count and entropy bounds, and what the code retains.

Takens' theorem for generic pairs `(T, h)` in `Diff²(M) × C²(M, ℝ)` is **not yet
formalized here**. The `C²` topology on `Diff²(M)` is defined and the good pairs are proved
open in the product; what remains is that the conditions on `T` above, the periodic-point
conditions of Takens' generic diffeomorphisms, hold for a dense set of `C²`
diffeomorphisms (a Kupka–Smale-type theorem). See
[Open Problems](https://project-navi.github.io/takens-formalization/research/open-problems/).

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
