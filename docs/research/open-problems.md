# Open Problems

Formalization is not a closed process. Every proved theorem sharpens the boundary
between what is known and what remains open. The problems below are genuine research
targets --- contributions at any tier are welcome, and negative results count.

If you are interested in working on any of these, open an issue or reach out on
[Zulip](https://leanprover.zulipchat.com/).

---

## Tier 1 --- Accessible

### Finite-horizon corollaries of the injectivity iff

**Status:** Skeleton exists (`TakensDiscrete.lean`), no definitions frozen.

**Problem.** The headline theorem `delayEmbedding_injective_iff_separatesOrbits`
characterizes injectivity of the delay embedding in terms of orbit separation.
The companion `exists_separatingWindow_iff` shows that, on a finite state space,
a separating window exists iff orbits eventually disagree under observation. What
remains is to extract concrete corollaries: explicit window-length bounds from
`coincidenceLength`, cardinality estimates on the image of the delay map for
specific system classes, and decidability results for finite dynamical systems.

**Why it matters.** These corollaries are what practitioners actually compute.
The iff theorem is the engine; the corollaries are the interface.

**Starting point.** Read `DelayWindow.lean` (the iff theorem and
`coincidenceLength` definition) and `TakensDiscrete.lean` (the empty skeleton).
The `IteratePeriod.lean` bridge lemmas connecting to Mathlib's `PeriodicPts` API
will be useful for any corollary involving periodic orbits.

---

## Tier 2 --- Intermediate

### High-dimensional Sard via Morse--Sard induction

**Status:** Deferred to gate 3. Equidimensional and low-dimensional cases proved
in `SardInfra.lean`. The high-dimensional case is the only remaining gap.

**Problem.** Prove that for a C^k map f : E -> F between finite-dimensional real
normed spaces with finrank E > finrank F, the set of critical values has measure
zero, provided k >= max(1, finrank E - finrank F + 1). This is the deep case of
Sard's theorem, requiring induction on the vanishing order of derivatives at
critical points.

The standard proof (following Sternberg or Hirsch) stratifies the critical set
by the order of vanishing of derivatives, bounds each stratum by a covering
argument, and closes by induction on dimension. The regularity requirement
C^{n-m+1} (where n = finrank E, m = finrank F) is sharp --- counterexamples
exist at lower regularity.

**Why it matters.** This is the only component needed to complete the `SardInfra`
typeclass, which currently axiomizes `sard_of_finrank_gt` as a placeholder. Once
proved, the typeclass can be replaced with a concrete instance, eliminating the
last axiom boundary in the project.

**Starting point.** `SardInfra.lean` contains the definitions (`criticalSet`,
`criticalValues`) and the proved equidimensional case (`sard_equidim`,
`sard_equidim_general`) and low-dimensional case (`sard_low_dim`). The Mathlib
dependencies are already identified: the Jacobian area formula
(`addHaar_image_le_lintegral_abs_det_fderiv`) and Hausdorff dimension
(`dimH`, `ContDiffOn.dimH_image_le`). The inductive step will likely require
Taylor expansion machinery from `Mathlib.Analysis.Calculus.Taylor`.

---

## Tier 3 --- Research-grade

### Genericity via parametric transversality

**Status:** Blocked on Sard + transversality infrastructure. No skeleton exists.

**Problem.** Prove the "generic pairs" result from Takens 1981: for a compact
manifold M of dimension m, the set of pairs (T, h) where the delay embedding
with 2m+1 delays is injective is residual (and hence dense) in the space of
diffeomorphisms cross observations, with the C^2 topology.

This requires three ingredients that are not yet formalized:

1. **Sard's theorem** (full version) --- the high-dimensional case above.
2. **Parametric transversality** --- if a family of maps F_t is transverse to a
   submanifold, then F_t is transverse for almost every t. This is the mechanism
   that converts "measure zero failure set" (Sard) into "residual success set"
   (Baire category).
3. **Jet transversality** --- the multijet extension of the delay map must be
   transverse to the diagonal, which requires working in jet bundles.

**Why it matters.** This is what makes Takens' theorem practically useful. The
injectivity iff (Route B) characterizes *when* the embedding works. The
genericity theorem says it works *generically* --- for "almost every" system, no
special conditions are needed. Without genericity, the theorem is a
characterization; with it, the theorem is a guarantee.

**Starting point.** The smooth embedding chain in `SmoothTakens.lean` (compact +
injective -> closed embedding -> homeomorphism onto image) provides the
topological half. The measure-theoretic half requires `SardInfra` plus
transversality machinery that does not yet exist in Mathlib. The Lean/Mathlib
manifold library (`Mathlib.Geometry.Manifold`) has smooth manifolds and tangent
bundles but not jet bundles or transversality.

---

## Tier 4 --- Theoretical

### Sauer--Yorke--Casdagli generalization

**Status:** No Mathlib infrastructure. Requires foundational library work.

**Problem.** Prove the Sauer--Yorke--Casdagli extension of Takens' theorem: if a
compact set A has box-counting dimension d, then for a prevalent set of
observations, the delay embedding with 2d+1 delays is injective on A. Here
"prevalent" replaces "residual" --- it is a measure-theoretic notion of genericity
in infinite-dimensional spaces, rather than a topological one.

This requires two pieces of infrastructure absent from Mathlib:

1. **Prevalence theory.** A subset S of a topological vector space is *shy* if
   there exists a compactly supported probability measure mu such that
   mu(S + v) = 0 for all v. The complement of a shy set is *prevalent*. This is
   the infinite-dimensional analogue of "full Lebesgue measure." The basic theory
   (sigma-ideal properties, relationship to Baire category, Hunt--Sauer--Yorke
   foundational results) would need to be built from scratch.

2. **Box-counting dimension.** The upper and lower box-counting dimensions
   (Minkowski dimensions) are defined via covering numbers of epsilon-balls.
   Mathlib has Hausdorff dimension (`dimH`) but not box-counting dimension.
   The two coincide for sufficiently regular sets but diverge in general, and the
   Sauer--Yorke--Casdagli result specifically uses box-counting dimension.

**Why it matters.** Takens' original theorem applies to smooth manifolds. Real
attractors are typically fractal --- they have finite box-counting dimension but
are not manifolds. The Sauer--Yorke--Casdagli generalization is the version that
actually applies to the strange attractors encountered in practice, including
those analyzed by [navi-SAD](https://project-navi.github.io/navi-SAD/theory/takens-embedding/).

**Starting point.** The prevalence theory foundational paper is Hunt, Sauer, and
Yorke, "Prevalence: a translation-invariant `almost every' on
infinite-dimensional spaces" (Bull. AMS 27, 1992). For box-counting dimension,
Falconer's *Fractal Geometry* (3rd ed.) is the standard reference. Neither topic
has existing Mathlib formalizations, so this is genuinely foundational library
work.
