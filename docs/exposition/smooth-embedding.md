# Smooth Embedding

Let \(M\) be a manifold modelled on a \(d\)-dimensional real space, \(T : M \to M\) the
dynamics and \(h : M \to \mathbb{R}\) the observation. Takens' theorem [Takens1981] concerns
the delay map \(\Phi_{2d+1}(x) = (h(x), h(Tx), \dots, h(T^{2d}x))\). This page follows the
formal argument from the topological embedding chain to generic observations.

## The embedding chain

<div class="theorem-block" markdown>
<span class="badge badge--proved">Proved</span>
<span class="theorem-name">(smoothDelayMap_isClosedEmbedding)</span>

If \(X\) is compact, \(T\) and \(h\) are continuous and the delay map is injective, then it
is a closed embedding, and a homeomorphism onto its image
(`smoothDelayMapRangeHomeomorph`).
</div>

A continuous injection from a compact space to a Hausdorff space is a closed embedding.
`smoothDelayMap` is kept as a name for compatibility; it is `delayEmbedding`
(`smoothDelayMap_eq_delayEmbedding`).

## The differential

For \(C^r\) data the delay map is \(C^r\) (`contMDiff_delayEmbedding`). Its differential has
coordinates given by the *delayed covectors*

$$\ell_i(x) = Dh_{T^i x} \circ D(T^i)_x : T_x M \to \mathbb{R}, \qquad i < k$$

(`delayCovector`, `mfderiv_delayEmbedding_apply`).

<div class="theorem-block" markdown>
<span class="badge badge--proved">Proved</span>
<span class="theorem-name">(injective_mfderiv_delayEmbedding_iff_span)</span>

The delay map is an immersion at \(x\) iff the delayed covectors \(\ell_0(x), \dots,
\ell_{k-1}(x)\) span the cotangent space.
</div>

Consequently an immersion needs \(k \ge d\) (`finrank_le_of_injective_mfderiv_delayEmbedding`),
and for \(T = \mathrm{id}\) in dimension \(d \ge 2\) every covector equals \(Dh_x\), so no
observation and no number of delays gives an immersion
(`not_injective_mfderiv_delayEmbedding_id`). This is why the classical theorem is about
generic *pairs* \((T, h)\) and not about generic \(h\) for an arbitrary fixed \(T\).

An `IsContMDiffEmbedding` is a \(C^r\) map with injective differentials that is a topological
embedding. On a compact manifold an injective immersion is one
(`isContMDiffEmbedding_of_injective`); the quarter turn of the circle observed by its first
coordinate is a worked example, embedded by any \(k \ge 2\) delays
(`isContMDiffEmbedding_delayEmbedding_quarterTurn_iff`).

## Generic observations in a finite family

Perturb the observation inside a finite family \(\varphi_1, \dots, \varphi_N\):
\(h_a = h + \sum_i a_i \varphi_i\) (`perturbObservation`). Its delay map is affine in \(a\).

<div class="theorem-block" markdown>
<span class="badge badge--proved">Proved</span>
<span class="theorem-name">(ae_isContMDiffEmbedding_delayEmbedding_perturb)</span>

Let \(M\) be compact and \(T\), \(h\), \(\varphi_i\) be \(C^2\), and \(k > 2d\). Suppose that
along every nonzero tangent vector the differentials of the delay maps of the \(\varphi_i\)
span \(\mathbb{R}^k\), and that at any two distinct points the differences of their delay
vectors span \(\mathbb{R}^k\). Then for almost every \(a\) the delay map of \(h_a\) is a
\(C^2\) embedding.
</div>

The proof works in extended charts, countably many by second countability. In a chart the
delay map of \(h_a\) is an affine family whose derivative in \(a\) is onto by the span
conditions. For immersion, the bad pairs (point, unit direction) form a set of dimension
\(2d - 1 < k\); for injectivity, the bad pairs of points form a set of dimension
\(2d < k\). In both cases the bad parameters are the projection of a level set of too small
dimension, which is Haar-null (`ae_forall_ne_of_hasStrictFDerivAt`); no appeal to Sard's
theorem is needed.

## Where the span conditions come from

A family *interpolates values* at \(N\) points if any values at any \(n \le N\) distinct
points are attained by a combination of it (`InterpolatesValues`), and *interpolates
derivatives* similarly for directional derivatives (`InterpolatesDerivatives`).

- **Separation** (`surjective_sum_smul_sub_delayEmbedding`). Let \(T\) be injective without
  periodic points of period at most \(2k - 2\). If the windows of \(x\) and \(y\) are
  disjoint, the \(2k\) points are distinct and the coordinates can be prescribed
  independently. Otherwise \(y = T^m x\) (or the reverse) with \(0 < m < k\), and the
  coordinates of the difference are \(v_j - v_{j+m}\) for the values \(v\) along one orbit
  segment; this triangular system has the explicit solution `telescope_sub`.
- **Immersion** (`surjective_sum_smul_mvfderiv_delayEmbedding`). If \(x, \dots, T^{k-1}x\)
  are distinct and the differentials of \(T\) are injective, the vectors
  \(D(T^i)_x v\) are nonzero at distinct points, and the family prescribes the derivatives
  of the \(\varphi_i\) along them independently.

An explicit family on a compact smooth manifold comes from a Whitney embedding
\(e : M \to \mathbb{R}^n\) (Mathlib's `exists_embedding_euclidean_of_compact`) and the moment
functionals \(\ell_t(q) = \sum_r t^r q_r\): for \(q \ne 0\), \(t \mapsto \ell_t(q)\) is a
nonzero polynomial of degree less than \(n\), so finitely many values of \(t\) suffice to
avoid any given finite set of nonzero vectors (`exists_forall_momentFunctional_ne_zero`).
The functions \(x \mapsto \ell_t(e(x))^s\) then interpolate values and derivatives by
Lagrange interpolation (`interpolatesValues_momentFamily`,
`interpolatesDerivatives_momentFamily`).

<div class="theorem-block" markdown>
<span class="badge badge--proved">Proved</span>
<span class="theorem-name">(exists_family_forall_ae_isContMDiffEmbedding_delayEmbedding)</span>

**Takens' theorem for maps without short periodic orbits.** On a compact smooth
\(d\)-manifold there are finitely many smooth functions \(\varphi_q\) such that, for every
injective \(C^2\) map \(T\) with injective differentials and no periodic points of period
at most \(4d\), and every \(C^2\) observation \(h\), the delay map of
\(h + \sum_q a_q \varphi_q\) with \(2d + 1\) coordinates is a \(C^2\) embedding for
Lebesgue-almost every \(a\), in particular for some \(a\) of arbitrarily small norm
(`exists_family_forall_exists_isContMDiffEmbedding_delayEmbedding`).
</div>

## What is not here

The statement above is an almost-every statement in one finite-dimensional family, for a
fixed map with no periodic points of period at most \(4d\). Takens' theorem for generic
pairs needs, in addition:

- periodic points of period at most \(2d\), where every delay coordinate repeats and the
  span conditions fail for every family; for generic \(T\) such points are finitely many,
  with simple eigenvalues, and need a separate local argument;
- the genericity of those conditions on \(T\) in the space of \(C^2\) diffeomorphisms;
- the \(C^2\) topology on pairs, openness of the embedding condition, and the
  Baire-category step from "almost every member of a family" to a residual set.

See [Open Problems](../research/open-problems.md).

## References

- [Takens1981] F. Takens, *Detecting strange attractors in turbulence*, Lecture Notes in
  Mathematics 898 (1981), 366--381.
- [SauerYorkeCasdagli1991] T. Sauer, J. A. Yorke, M. Casdagli, *Embedology*, J. Stat. Phys.
  65 (1991), 579--616.
- [Huke2006] J. P. Huke, *Embedding nonlinear dynamical systems: a guide to Takens'
  theorem*, MIMS EPrint 2006.26.
