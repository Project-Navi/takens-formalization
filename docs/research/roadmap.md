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
- **Genericity for a fixed map.** Generic immersion and separation in finite families;
  Takens' theorem for a fixed map satisfying the periodic-point conditions, both for almost
  every member of a finite family
  (`exists_family_forall_ae_isContMDiffEmbedding_delayEmbedding_of_periodic`) and as an open
  dense set of observations in the \(C^2\) topology
  (`isOpen_and_dense_setOf_isContMDiffEmbedding_delayEmbedding`).

Every selected declaration depends only on `propext`, `Classical.choice` and `Quot.sound`,
and CI checks this, the build with warnings as errors, the linter, the documented names and
a fresh kernel replay on every pull request.

---

## Next: Takens' theorem for generic pairs

In order of dependence (details in [Open Problems](open-problems.md)):

1. Genericity of the periodic-point conditions: for an open dense set of \(C^2\)
   diffeomorphisms, finitely many periodic points of period at most \(4d\), with distinct
   eigenvalues at those of period at most \(2d\) (a Kupka--Smale-type theorem).
2. The \(C^2\) topology on \(\mathrm{Diff}^2(M)\), continuity of the delay map in the pair,
   and openness of good pairs.
3. The assembly: good pairs are open, and dense because their fibres over a dense set of
   maps are dense.

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
