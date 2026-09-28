# Roadmap

Where the formalization stands and what comes next.

---

## Current state

- **Finite state spaces and ordinal codes.** Complete for the questions posed: injectivity
  and orbit separation, the exact separating horizon with the sharp bound \(N-1\), a sound
  and complete decision procedure, reconstruction on the delay image, and the ordinal code
  with its counts, entropy and quotient.
- **Sard's theorem.** Proved in all dimensions at the sharp finite regularity
  \(r \ge \dim E - \dim F + 1\), with local and open-set versions (`sard`).
- **Smooth delay maps.** Regularity, the differential, the immersion criterion, and the
  embedding criterion on compact manifolds.
- **Genericity.** Generic immersion and separation in finite families, and Takens' theorem
  for a fixed map without periodic points of period at most \(4d\)
  (`exists_family_forall_ae_isContMDiffEmbedding_delayEmbedding`).

Every selected declaration depends only on `propext`, `Classical.choice` and `Quot.sound`,
and CI checks this, the build with warnings as errors, the linter, the documented names and
a fresh kernel replay on every pull request.

---

## Next: Takens' theorem for generic pairs

In order of dependence (details in [Open Problems](open-problems.md)):

1. Periodic points of period at most \(2d\): observability at periodic points with simple
   eigenvalues, local injectivity near them, and avoidance for pairs of positive
   codimension.
2. Periods between \(2d + 1\) and \(4d\), by a dimension count over finitely many
   periodic orbits.
3. Genericity of the periodic-point conditions for \(C^2\) diffeomorphisms.
4. The \(C^2\) topology on pairs, openness of embeddings, continuity of the delay map in
   the pair, and the Baire-category assembly.

---

## Upstreaming

`OrdinalPattern`, `DelayWindow` with `TakensDiscrete`, and the lemmas in
`TakensFormal/ForMathlib/` are written to Mathlib's conventions. Proposals start with a
Zulip discussion; the Sard port is coordinated with its upstream author.

---

## Long term: fractal sets

The Sauer--Yorke--Casdagli theorem (box-counting dimension, prevalence) is a separate
extension that needs prevalence theory and box-counting dimension in Mathlib; see
[Open Problems](open-problems.md).
