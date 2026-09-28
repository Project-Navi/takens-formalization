# Glossary

Terms used throughout the formalization, with the page where each is developed.

---

**almost every (in a finite family)**
: For a family \(h + \sum_i a_i \varphi_i\) with finitely many coefficients, a property
holds for almost every coefficient vector if the exceptions have Lebesgue (equivalently,
additive Haar) measure zero. This is a statement about one finite-dimensional family; it is
neither residuality in an infinite-dimensional space nor prevalence. See
[Smooth Embedding](../exposition/smooth-embedding.md).

**axiom record**
: The output of `#print axioms` for a declaration. CI accepts only `propext`,
`Classical.choice` and `Quot.sound`. See [Axiom Dashboard](axiom-dashboard.md).

**closed embedding**
: A continuous injective map that is a homeomorphism onto a closed image. On a compact
space every continuous injection into a Hausdorff space is one. See
[Smooth Embedding](../exposition/smooth-embedding.md).

**\(C^r\) embedding**
: A \(C^r\) map with injective differential at every point that is a topological embedding
(`IsContMDiffEmbedding`). See [Smooth Embedding](../exposition/smooth-embedding.md).

**coincidence length**
: The first time at which the observations of two orbits differ, or \(\infty\).
See [Coincidence Length](../exposition/coincidence-length.md).

**critical set, critical values**
: The points where the derivative is not surjective, and their image. Sard's theorem says
the critical values have measure zero. See [Sard's Theorem](../exposition/sard-infrastructure.md).

**delay map**
: \(x \mapsto (h(x), h(Tx), \dots, h(T^{k-1}x))\), `delayEmbedding` in Lean. See
[Delay Embedding](../exposition/delay-embedding.md).

**delayed covector**
: \(Dh_{T^i x} \circ D(T^i)_x\), the \(i\)-th coordinate of the differential of the delay
map (`delayCovector`). See [Smooth Embedding](../exposition/smooth-embedding.md).

**generic pair**
: A pair \((T, h)\) in a residual (comeagre) subset of
\(\mathrm{Diff}^2(M) \times C^2(M, \mathbb{R})\) with the \(C^2\) topology. Residuality is a
Baire-category notion and does not mean probability one. Takens' theorem for generic pairs
is not yet formalized here. See [Open Problems](../research/open-problems.md).

**immersion**
: A map whose differential is injective at every point. For a delay map this holds at
\(x\) iff the delayed covectors span the cotangent space.

**interpolating family**
: A finite family of functions whose combinations take any prescribed values, or
directional derivatives, at any bounded number of distinct points (`InterpolatesValues`,
`InterpolatesDerivatives`). See [Smooth Embedding](../exposition/smooth-embedding.md).

**Moreira's theorem**
: A sharpening of Sard's theorem that bounds the Hausdorff measure of the image of the
points of low rank of a \(C^{k+(\alpha)}\) map [Moreira2001]; ported here from a Lean proof
by Yury Kudryashov. See [Sard's Theorem](../exposition/sard-infrastructure.md).

**observation**
: The function \(h\) (or \(\alpha\)) applied to each state before delays are taken.

**ordinal pattern**
: The permutation that sorts a tie-free vector. It depends only on the order of the
entries. See [Ordinal Compression](../exposition/ordinal-compression.md).

**orbit separation**
: The observation distinguishes any two distinct states within the first \(k\) iterates;
equivalent to injectivity of the delay map (`SeparatesOrbits`).

**prevalence**
: A measure-theoretic notion of "almost every" in infinite-dimensional spaces, used by
Sauer, Yorke and Casdagli. Not formalized here. See
[Open Problems](../research/open-problems.md).

**separating horizon**
: The least window length that separates orbits, or \(\infty\) (`separatingHorizon`); at
most \(N - 1\) on \(N\) states when finite. See
[Coincidence Length](../exposition/coincidence-length.md).

**span condition**
: The hypothesis of the generic-family theorems: the parameter derivative of the family
is onto. For delay maps, the differentials, or the differences, of the delay maps of the
family must span \(\mathbb{R}^k\).

**strictly increasing, strictly decreasing**
: `StrictMono` and `StrictAnti`. Ordinal codes are unchanged by strictly increasing
transformations of the observation and relabeled by index reversal under strictly
decreasing ones; merely monotone transformations can create ties.

**tie-free window**
: A delay window with pairwise distinct entries (`WindowDistinct`), needed for an ordinal
pattern.
