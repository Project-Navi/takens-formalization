[![Lean CI](https://github.com/Project-Navi/takens-formalization/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/Project-Navi/takens-formalization/actions/workflows/lean_action_ci.yml)
[![Docs](https://github.com/Project-Navi/takens-formalization/actions/workflows/docs.yml/badge.svg)](https://github.com/Project-Navi/takens-formalization/actions/workflows/docs.yml)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-orange)](LICENSE)

# Delay embeddings in Lean 4

A Lean 4 and Mathlib formalization of delay-coordinate reconstruction
`x ↦ (h x, h (T x), …, h (T^(k-1) x))`, from finite state spaces to compact manifolds.

## What is proved

- **Delay embeddings for maps without short periodic orbits.** On a compact smooth
  `d`-manifold there are finitely many smooth functions `φ q` such that, for every injective
  `C²` map `T` with injective differentials and no periodic points of period at most `4d`,
  and every `C²` observation `h`, the delay map of `h + ∑ q, a q • φ q` with `2d + 1`
  coordinates is a `C²` embedding for Lebesgue-almost every coefficient vector `a`
  (`exists_family_forall_ae_isContMDiffEmbedding_delayEmbedding`).
- **Sard's theorem at finite regularity.** For `f : E → F` of class `C^r` with
  `r ≥ dim E - dim F + 1`, the critical values are Haar-null (`sard`), with local and
  open-set versions, via a port of Moreira's theorem.
- **Smooth delay maps.** Regularity, the differential and an immersion criterion; a compact
  injective immersion is a `C^r` embedding; the identity never immerses in dimension `≥ 2`.
- **Finite state spaces.** The exact separating horizon, the sharp bound `N - 1` (attained),
  a sound and complete decision procedure, and reconstruction of the dynamics on the image.
- **Ordinal codes.** Ordinal patterns, their behavior under strictly increasing and strictly
  decreasing transformations, pattern-count and entropy bounds, and what the code retains.

Takens' theorem for generic pairs `(T, h)` in the `C²` topology is **not yet formalized
here**: periodic points of small period, the genericity of `T`, and the Baire-category
assembly remain. The result above is an almost-every statement in a finite family, not a
residual set.

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
