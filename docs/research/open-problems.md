# Open Problems

Extensions not formalized here. Each item is a classical result or a missing piece of
library infrastructure, not an open mathematical problem.
Contributions are welcome; open an issue or write on
[Zulip](https://leanprover.zulipchat.com/).

---

## Takens' theorem for generic pairs: formalized

Takens' theorem for generic pairs [Takens1981] is formalized here in the \(C^2\) topology
(`isOpen_and_dense_setOf_isContMDiffEmbedding_delayEmbedding_pair`); see
[Smooth Embedding](../exposition/smooth-embedding.md). What follows are extensions.

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
