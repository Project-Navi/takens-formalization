# Roadmap

This page describes where the formalization stands and where it is headed. The
progression follows a gate model: each gate represents a level of enforcement and
completeness, not a calendar deadline. Gates are passed when the criteria are met,
not when a date arrives.

---

## Current state: Gate 1.5 --- sorry-enforced

**42 declarations. Zero sorry. Zero unexpected axioms.**

The formalization has two independent proof routes:

**Route B (discrete)** is complete at the level of the core embedding theory.
The headline theorem `delayEmbedding_injective_iff_separatesOrbits` characterizes
when the delay embedding is injective. The companion theorems ---
`exists_separatingWindow_iff` (separating windows exist iff orbits eventually
disagree), `coincidenceLength` (the index of first disagreement), and the ordinal
compression chain (`ordinalDelayMap` with pattern-count bounds `le_factorial` and
`le_period`) --- give a complete discrete toolkit. All proved, no axioms beyond
`propext`, `Classical.choice`, `Quot.sound`.

**Route A (smooth)** has two layers. The embedding chain in `SmoothTakens.lean`
--- continuity, closed embedding, homeomorphism onto image --- is proved and fully
axiom-free. The Sard infrastructure in `SardInfra.lean` proves the
equidimensional case (via the Jacobian area formula), the low-dimensional case
(via Hausdorff dimension), and the general equidimensional case (via continuous
linear equivalences). Also proved, also axiom-free.

**Enforcement.** CI runs `lake build --wfail` (warnings as errors) and
`scripts/check-axioms.sh` (rejects `sorryAx`) on every push and pull request.
The sorry-free invariant is machine-enforced, not just social convention.

---

## Gate 3 --- SardInfra typeclass and axiom allowlist

The next gate has two components:

### 1. SardInfra typeclass

The equidimensional and low-dimensional Sard cases are *proved*, not axiomized.
The remaining gap is the high-dimensional case: when finrank E > finrank F, the
Morse--Sard inductive argument requires C^{n-m+1} regularity and induction on
the vanishing order of derivatives at critical points.

The plan is to axiomize *only* this one case as a typeclass field
`sard_of_finrank_gt`, following the `PDEInfra` pattern from cd-formalization. The
proved cases remain as concrete theorems. This keeps the axiom surface minimal
and clearly delineated.

Designing the typeclass is the gating constraint --- getting the interface right
(what hypotheses, what universe levels, what relationship to the proved cases)
determines everything downstream.

### 2. Axiom allowlist

Once the typeclass is designed, `scripts/check-axioms.sh` will be upgraded from
"reject `sorryAx`" to "reject any axiom not on the allowlist." The allowlist will
contain exactly `propext`, `Classical.choice`, `Quot.sound`, and whatever the
`SardInfra` typeclass introduces. Any unexpected axiom fails CI.

---

## Future --- parametric transversality and genericity

With the SardInfra typeclass in place, the path to the full genericity theorem
becomes:

1. **Parametric transversality.** If a parameterized family of smooth maps is
   transverse to a submanifold, then almost every member of the family is
   transverse. This converts Sard's "measure zero failure set" into a "residual
   success set" via Baire category.

2. **Jet transversality for delay maps.** The multijet extension of the delay map
   must be transverse to the diagonal in the appropriate jet bundle. This is where
   the "2m+1 delays suffice" dimension count comes from.

3. **Genericity theorem.** For a compact m-dimensional manifold, the set of
   (diffeomorphism, observation) pairs for which the delay embedding with 2m+1
   delays is injective is residual in the C^2 topology.

None of this infrastructure exists in Mathlib today. Jet bundles, transversality,
and the C^k topology on function spaces are not formalized. This is research-grade
work --- see [Open Problems](open-problems.md) for details.

---

## Future --- Mathlib upstream candidates

Two files are designed as upstream candidates:

- **`OrdinalPattern.lean`** --- the Bandt--Pompe ordinal pattern extractor. A
  natural addition to Mathlib, likely under `Combinatorics` or
  `Dynamics.TimeSeries`. Five declarations: the `IsOrdinalPatternOf` predicate,
  the `ordinalPattern` extraction function, existence/uniqueness, monotone
  invariance, and surjectivity.

- **`DelayWindow.lean`** --- the delay coordinate map for finite dynamical
  systems. Natural home under `Dynamics`. Core declarations: `delayEmbedding`,
  `SeparatesOrbits`, the injectivity iff, continuity, `coincidenceLength`, and
  `exists_separatingWindow_iff`.

The upstream process follows Mathlib conventions: post the design to Zulip first,
submit as small focused PRs, disclose AI-assisted development. No PRs have been
submitted yet --- the Zulip discussion is gated on completing the finite-horizon
corollaries in `TakensDiscrete.lean` so the contribution is self-contained.

---

## Long-term --- Sauer--Yorke--Casdagli

The fractal generalization of Takens' theorem (box-counting dimension replacing
manifold dimension, prevalence replacing Baire genericity) requires two pieces of
Mathlib infrastructure that do not exist:

- **Prevalence theory** (shy sets, Hunt--Sauer--Yorke 1992)
- **Box-counting dimension** (Minkowski dimension, distinct from Hausdorff
  dimension already in Mathlib)

This is foundational library work, not specific to this project. If either topic
is formalized in Mathlib by others, the path here shortens considerably. In the
meantime, the formalization covers the smooth-manifold version of Takens' theorem,
which is the version most cited in the dynamical systems literature.

See [Open Problems](open-problems.md) for a fuller description of the
mathematical requirements.
