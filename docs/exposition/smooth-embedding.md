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

## Short periodic orbits

Takens' generic maps have periodic points of small period, where every delay coordinate
repeats. Two conditions on \(T\) replace the absence of such points:

- the points of period at most \(4d\) form a countable set (for generic \(T\), a finite one);
- at a point \(z\) of minimal period \(p \le 2d\), with \(A = D(T^p)_z\), some covector
  \(\omega\) detects every nonzero vector through \(\omega \circ A^q\), \(q < d\). This
  observability condition holds when \(A\) has \(d\) distinct eigenvalues.

<div class="theorem-block" markdown>
<span class="badge badge--proved">Proved</span>
<span class="theorem-name">(exists_family_forall_ae_isContMDiffEmbedding_delayEmbedding_of_periodic)</span>

**Takens' theorem for a fixed map, in a finite family.** On a compact smooth
\(d\)-manifold there are finitely many smooth functions \(\varphi_q\) such that, for every
injective \(C^2\) map \(T\) with injective differentials satisfying the two conditions, and
every \(C^2\) observation \(h\), the delay map of \(h + \sum_q a_q \varphi_q\) with \(2d + 1\)
coordinates is a \(C^2\) embedding for Lebesgue-almost every \(a\).
</div>

The proof (`ae_isContMDiffEmbedding_delayEmbedding_perturb_of_periodic`) splits points and
pairs of points.

- **Immersion at a periodic point** (`exists_injective_mfderiv_delayEmbedding_perturb_of_periodic`).
  Let \(z\) have minimal period \(p \le 2d\) and \(Q = \lfloor 2d/p \rfloor\), so that
  \(d \le pQ \le 2d\). The family also interpolates covectors
  (`interpolatesCovectors_momentFamily`), so the differential of the observation at
  \(T^r z\), \(r < p\), can be prescribed to make the delayed covector of index \(r + qp\)
  equal to \(\omega \circ A^{rQ + q}\). The exponents \(rQ + q\) cover \(0, \dots, d - 1\), so
  the differential of the delay map is injective at \(z\) for one coefficient vector.
  Injectivity is a polynomial condition in the coefficients, and a nonzero polynomial
  vanishes only on a null set (`MvPolynomial.ae_eval_ne_zero`); so it holds for almost every
  coefficient vector (`ae_injective_add_sum`).
- **Immersion elsewhere and separation involving an aperiodic point** use the span
  conditions of the previous section (`surjective_sum_smul_sub_delayEmbedding_of_aperiodic`).
- **Pairs of periodic points** are countably many, and each is separated for almost every
  coefficient vector by the first coordinate alone (`ae_delayEmbedding_perturb_ne_of_ne`).

## The \(C^2\) topology and open dense observations

The space \(C^n(M, F)\) of \(C^n\) maps into a normed space carries the weak \(C^n\)
topology (`ContMDiffMap.instTopologicalSpace`): a basic neighbourhood of \(f\) consists of
the maps whose chart derivatives of order at most \(n\) are uniformly \(\varepsilon\)-close
to those of \(f\) on finitely many compact sets of chart coordinates
(`ContMDiffMap.eventually_forall_dist_jet_lt`). On a compact manifold this is the Whitney
\(C^n\) topology [Hirsch1976].

<div class="theorem-block" markdown>
<span class="badge badge--proved">Proved</span>
<span class="theorem-name">(exists_forall_injective_of_near)</span>

**Stability of embeddings.** An injective \(C^1\) immersion of a compact manifold into a
normed space has a \(C^1\) neighbourhood of injective immersions.
</div>

Near each point the chart derivative is bounded below, and a map whose chart derivative is
close on a closed ball is injective there, with injective derivatives, by the mean value
inequality (`exists_closedBall_forall_injOn`). Finitely many balls cover \(M\); the pairs of
points not in a common ball form a compact set on which the map separates points by some
\(\delta > 0\). Precomposition with a fixed \(C^1\) map preserves \(C^1\)-closeness
(`exists_forall_near_comp`), so the delay map depends continuously on the observation.

<div class="theorem-block" markdown>
<span class="badge badge--proved">Proved</span>
<span class="theorem-name">(isOpen_and_dense_setOf_isContMDiffEmbedding_delayEmbedding)</span>

**Takens' theorem for a fixed map, in the \(C^2\) topology.** For \(T\) as above, the \(C^2\)
observations whose delay map with \(2d + 1\) coordinates is a \(C^2\) embedding form an open
dense subset of \(C^2(M, \mathbb{R})\).
</div>

Openness holds for every \(C^2\) map \(T\) and any number of coordinates
(`isOpen_setOf_isContMDiffEmbedding_delayEmbedding`). Density comes from the finite family:
\(h + \sum_q a_q \varphi_q \to h\) as \(a \to 0\) (`ContMDiffMap.continuous_perturb`), and
almost every such perturbation is good
(`dense_setOf_isContMDiffEmbedding_delayEmbedding`).

## What is not here

The conditions on \(T\) are those of Takens' generic diffeomorphisms, but their genericity
is not formalized. Takens' theorem for generic pairs \((T, h)\) needs, in addition:

- a Kupka--Smale-type theorem: for an open dense set of \(C^2\) diffeomorphisms, the
  periodic points of period at most \(4d\) are finitely many and those of period at most
  \(2d\) satisfy the observability condition;
- the \(C^2\) topology on \(\mathrm{Diff}^2(M)\), with the delay map continuous in
  \((T, h)\), so that the good pairs form an open set;
- the assembly: an open set of pairs whose fibre over each map of a dense set is dense is
  dense.

See [Open Problems](../research/open-problems.md).

## References

- [Takens1981] F. Takens, *Detecting strange attractors in turbulence*, Lecture Notes in
  Mathematics 898 (1981), 366--381.
- [SauerYorkeCasdagli1991] T. Sauer, J. A. Yorke, M. Casdagli, *Embedology*, J. Stat. Phys.
  65 (1991), 579--616.
- [Huke2006] J. P. Huke, *Embedding nonlinear dynamical systems: a guide to Takens'
  theorem*, MIMS EPrint 2006.26.
- [Hirsch1976] M. W. Hirsch, *Differential Topology*, Graduate Texts in Mathematics 33,
  Springer (1976).
