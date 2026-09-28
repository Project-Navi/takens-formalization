# Sard's Theorem

Sard's theorem [Sard1942] says that the critical values of a sufficiently smooth map have
measure zero. Here \(E\) and \(F\) are finite-dimensional real normed spaces,
\(n = \dim E\), \(m = \dim F\), and "measure zero" means zero for every additive Haar
measure on \(F\).

| Case | Regularity | Method | Declaration |
|------|-----------|--------|-------------|
| \(n = m\) | \(C^1\) | Jacobian area formula | `sard_equidim_general_of_contDiff` |
| \(n < m\) | \(C^1\) | Hausdorff dimension | `sard_low_dim_of_contDiff` |
| all \(n\), \(m\) | \(C^r\), \(r \ge n - m + 1\) | Moreira's theorem | `sard` |

In the last row \(n - m\) is truncated subtraction, so for \(n \le m\) the condition is
\(r \ge 1\). The threshold cannot be lowered in general: [Whitney1935] gives a \(C^1\)
function on \(\mathbb{R}^2\) that is not constant on a connected set of critical points.

## Critical points

<div class="theorem-block" markdown>
<span class="badge badge--proved">Proved</span>
<span class="theorem-name">(criticalSet)</span>

The *critical set* of \(f : E \to F\) is \(\{x \mid Df(x) \text{ is not surjective}\}\), and
its image is the set of *critical values* (`criticalValues`).
</div>

For \(f : E \to E\) the critical set is the zero set of the Jacobian determinant
(`criticalSet_eq_det_zero`), and it is closed when \(f\) is \(C^1\)
(`isClosed_criticalSet`). A map into a zero-dimensional space has no critical points, since
every linear map onto \(\{0\}\) is surjective (`criticalSet_eq_empty_of_finrank_eq_zero`).

## Equal and lower dimension

<div class="theorem-block" markdown>
<span class="badge badge--proved">Proved</span>
<span class="theorem-name">(sard_equidim_of_contDiff)</span>

If \(f : E \to E\) is \(C^1\), its critical values have Haar measure zero.
</div>

The area formula bounds \(\mu(f(S))\) by \(\int_S |\det Df|\,d\mu\), which vanishes on the
critical set. For \(\dim E = \dim F\), a continuous linear equivalence reduces
\(f : E \to F\) to this case (`sard_equidim_general_of_contDiff`). For
\(\dim E < \dim F\), a differentiable image has Hausdorff dimension at most \(\dim E\), so
the whole image is Haar-null (`sard_low_dim_of_contDiff`). The original statements for
analytic maps (`sard_equidim`, `sard_low_dim`, `sard_equidim_general`) are kept as
corollaries.

## All dimensions

<div class="theorem-block" markdown>
<span class="badge badge--proved">Proved</span>
<span class="theorem-name">(sard)</span>

**Sard's theorem.** If \(f : E \to F\) is \(C^r\) with \(r \ge \dim E - \dim F + 1\), then
\(\mu(\operatorname{CritVal}(f)) = 0\) for every additive Haar measure \(\mu\) on \(F\).
</div>

Moreira's theorem [Moreira2001] bounds the size of the image of the points where the
derivative has rank at most \(p\): for a \(C^{k+(\alpha)}\) map on an \(n\)-dimensional
space, that image has zero \(s\)-dimensional Hausdorff measure for
\(s = p + (n - p)/(k + \alpha)\)
(`hausdorffMeasure_sardMoreiraBound_image_null_of_finrank_le`). For \(0 < m \le n\) take
\(p = m - 1\), \(k = n - m + 1\) and \(\alpha = 0\): a critical point has rank at most
\(m - 1\), and

$$s = (m-1) + \frac{n - m + 1}{n - m + 1} = m$$

(`coe_sardMoreiraBound_sub_add_one`). Zero \(m\)-dimensional Hausdorff measure in the
\(m\)-dimensional space \(F\) is zero Haar measure. The cases \(m = 0\) and \(n < m\) are
handled separately as above.

For the charts of a manifold the local forms are the useful ones: if \(f\) is \(C^r\) at
every point of a set \(s\), its critical values on \(s\) are null
(`addHaar_image_inter_criticalSet_eq_zero`), and likewise on an open set
(`addHaar_image_inter_criticalSet_eq_zero_of_contDiffOn`).

## Provenance of the port

`TakensFormal/ForMathlib/SardMoreira/` contains the part of Yury Kudryashov's Lean project
`urkud/SardMoreira` (commit `14bc8a1eeaedb14f9ae95e125c95a5eb4f47f8c5`, Apache 2.0) that the
proof of Moreira's theorem needs, ported from the Lean release it was written for to the
Mathlib pinned here. Each file keeps the upstream copyright line and records its source
file and the changes in a `## Provenance` section. The changes are renamed Mathlib API,
explicit arguments where elaboration changed, a compatibility option for definitional
unfolding in three files, one lemma dropped as a duplicate of Mathlib's, and one simp
attribute and one unused instance argument removed; no statement was weakened. `sard` and the chart-level wrappers in
`Sard` are new here.

## References

- [Sard1942] A. Sard, *The measure of the critical values of differentiable maps*, Bull.
  Amer. Math. Soc. 48 (1942), 883--890.
- [Moreira2001] C. G. T. de A. Moreira, *Hausdorff measures and the Morse-Sard theorem*,
  Publ. Mat. 45 (2001), 149--162.
- [Whitney1935] H. Whitney, *A function not constant on a connected set of critical points*,
  Duke Math. J. 1 (1935), 514--517.
