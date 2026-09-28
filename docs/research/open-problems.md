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

**Formalized here.** For a fixed map, the full statement in the \(C^2\) topology. Let \(T\)
be an injective \(C^2\) map with injective differentials such that (i) its points of period
at most \(4d\) form a countable set and (ii) at every point \(z\) of minimal period
\(p \le 2d\) some covector \(\omega\) detects every nonzero vector through
\(\omega \circ D(T^{qp})_z\), \(q < d\). Then the \(C^2\) observations whose delay map with
\(2d + 1\) coordinates is a \(C^2\) embedding form an open dense subset of
\(C^2(M, \mathbb{R})\) (`isOpen_and_dense_setOf_isContMDiffEmbedding_delayEmbedding`), for
the weak \(C^2\) topology defined through chart derivatives on compact windows
(`ContMDiffMap.instTopologicalSpace`). Almost every perturbation in one fixed finite family
is good (`exists_family_forall_ae_isContMDiffEmbedding_delayEmbedding_of_periodic`). See
[Smooth Embedding](../exposition/smooth-embedding.md).

**Remaining obligations.**

1. **Genericity of \(T\) (Kupka--Smale type).** An open dense set \(\mathcal{D}\) of \(C^2\)
   diffeomorphisms of \(M\) satisfies (i) and (ii): for \(T \in \mathcal{D}\), the periodic
   points of period at most \(4d\) are finitely many (nondegenerate: \(1\) is not an
   eigenvalue of \(D(T^p)_z\)), and at those of period at most \(2d\) the eigenvalues of
   \(D(T^p)_z\) are distinct, which gives (ii) through a cyclic vector of the transpose.
   This needs local perturbations of diffeomorphisms supported near an orbit, transversality
   of the graph of \(T^p\) to the diagonal, and an induction on the period.
2. **Assembly.** An open set of pairs whose fibre over each \(T\) in the dense set
   \(\mathcal{D}\) is dense (the fixed-map theorem above) is dense, hence open dense and
   residual.

**Formalized here, for pairs.** The \(C^n\) topology on \(C^n\) diffeomorphisms through
chart derivatives on both source and target (`Diffeomorph.instTopologicalSpace`), closeness
under composition and iteration (`BiChartWindow.exists_near_iterate`), and, with the
stability of embeddings (`exists_forall_injective_of_near`), the openness of the good pairs
in \(\mathrm{Diff}^2(M) \times C^2(M, \mathbb{R})\)
(`isOpen_setOf_isContMDiffEmbedding_delayEmbedding_pair`). Mathlib has no topology on
spaces of \(C^r\) maps between manifolds; `JetTopology` and `WeakTopology` provide them.

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
