# Open Problems

What remains to be formalized here, in order of dependence. Each item is a classical
result or a missing piece of library infrastructure, not an open mathematical problem.
Contributions are welcome; open an issue or write on
[Zulip](https://leanprover.zulipchat.com/).

---

## Takens' theorem for generic pairs

**Statement.** Let \(M\) be a compact smooth manifold of dimension \(d\). For \((T, h)\) in
an open dense subset of \(\mathrm{Diff}^2(M) \times C^2(M, \mathbb{R})\), with the \(C^2\)
topology, the delay map \(x \mapsto (h(x), h(Tx), \dots, h(T^{2d}x))\) is a \(C^2\)
embedding [Takens1981].

**Formalized here.** For a fixed injective \(C^2\) map \(T\) with injective differentials
and no periodic points of period at most \(4d\), one finite family of smooth functions
makes the delay map of \(h + \sum_q a_q \varphi_q\) a \(C^2\) embedding for almost every
\(a\), for every \(C^2\) observation \(h\)
(`exists_family_forall_ae_isContMDiffEmbedding_delayEmbedding`). The ingredients (generic
immersion and separation in finite families, the overlapping-window combinatorics, an
interpolating family) are in place; see [Smooth Embedding](../exposition/smooth-embedding.md).

**Remaining obligations.**

1. **Periodic points of period at most \(2d\).** At such points the delay coordinates
   repeat, and the span conditions fail for every family (a fixed point has all
   coordinates equal to \(h(x)\)). The classical argument assumes, for generic \(T\), that
   these points are finitely many and that \(DT^p\) has simple eigenvalues there; then a
   generic observation is an immersion at them (an observability, or Krylov, condition on
   the covector \(Dh\)) and separates them from other points. This needs the linear
   algebra of cyclic vectors, a local injectivity argument near the periodic orbits, and a
   version of the avoidance lemma for sets of pairs of positive codimension.
2. **Periods between \(2d + 1\) and \(4d\).** The present separation argument uses \(2k\)
   interpolation points, which is why it excludes periods up to \(4d\). Takens' hypothesis
   excludes only the short periods above; for periods \(p\) with \(2d < p \le 4d\) the
   overlapping windows of a periodic orbit give a cyclic system, and those pairs must be
   treated by a dimension count, using that such orbits are finitely many for generic
   \(T\).
3. **Genericity of \(T\).** The conditions of items 1 and 2 hold for an open dense set of
   \(C^2\) diffeomorphisms (a Kupka--Smale-type theorem for periodic points of bounded
   period).
4. **Topology and assembly.** The \(C^2\) topology on \(\mathrm{Diff}^2(M)\) and
   \(C^2(M, \mathbb{R})\), with a proved description through charts and derivatives;
   openness of the set of embeddings on a compact manifold; continuity of
   \((T, h) \mapsto\) delay map; and the step from "almost every member of a finite
   family" to a dense (and, with openness, residual) set.

Mathlib has smooth manifolds, the Whitney embedding of compact manifolds and the implicit
function theorem, which the present proofs use, but no topology on spaces of \(C^r\) maps
between manifolds.

---

## Sauer--Yorke--Casdagli: fractal sets and prevalence

A different extension [SauerYorkeCasdagli1991]: if \(A \subset \mathbb{R}^n\) is compact
with box-counting dimension \(d_A\), then for a *prevalent* set of \(C^1\) observations
the delay map with \(k > 2 d_A\) coordinates is injective on \(A\), under conditions on the
periodic points of \(T\) in \(A\).

This is not the classical theorem and is not claimed here. It needs two notions that
Mathlib lacks:

- **Prevalence** [HuntSauerYorke1992]: a set is *shy* if some compactly supported
  probability measure gives measure zero to all its translates; prevalent sets are the
  complements. It is a measure-theoretic notion of "almost every" in infinite dimensions,
  distinct from residuality.
- **Box-counting dimension** [Falconer2014], which differs from Hausdorff dimension (in
  Mathlib as `dimH`) for irregular sets.

The finite-family statements proved here (almost every coefficient vector) are the kind of
"probe" estimates such a proof uses, but no prevalence statement is proved.

---

## Upstreaming to Mathlib

Candidates, following Mathlib's process (discussion on Zulip first, small pull requests,
disclosure of AI assistance):

- `ordinalPattern` and its API (Mathlib has `Tuple.sort` but no ordinal patterns);
- `delayEmbedding` with orbit separation, coincidence length and the sharp horizon bound;
- `sard` and the port of Moreira's theorem, coordinated with the upstream author;
- the avoidance and generic-family lemmas in `TakensFormal/ForMathlib/`.

## References

- [Takens1981], [SauerYorkeCasdagli1991], [HuntSauerYorke1992], [Falconer2014]; see
  `docs/references.bib`.
