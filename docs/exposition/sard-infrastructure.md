# Sard Infrastructure

Sard's theorem (Sard, 1942) states that the set of *critical values* of a smooth map \(f : M \to N\) between manifolds has measure zero in \(N\). It is a foundational result in differential topology, underpinning transversality theory, Morse theory, and --- for this project --- the genericity argument in the smooth Takens embedding theorem.

This file builds the infrastructure for Sard's theorem in the setting of finite-dimensional real normed spaces. Three cases arise, distinguished by the relationship between \(\dim E\) and \(\dim F\):

| Case | Condition | Strategy | Status |
|------|-----------|----------|--------|
| **Equidimensional** | \(\dim E = \dim F\) | Jacobian area formula | Proved |
| **Low-dimensional** | \(\dim E < \dim F\) | Hausdorff dimension | Proved |
| **High-dimensional** | \(\dim E > \dim F\) | Morse--Sard induction | Deferred (gate 3) |

## Definitions

<div class="theorem-block" markdown>
<span class="badge badge--proved">Proved</span>
<span class="theorem-name">(criticalSet)</span>

**Definition.** The *critical set* of \(f : E \to F\) is

$$\operatorname{Crit}(f) \;=\; \bigl\{\, x \in E \;\big|\; Df(x) : E \to F \text{ is not surjective}\,\bigr\}.$$

</div>

<details>
<summary>Lean 4 statement --- <code>SardInfra.lean:76</code></summary>

```lean
def criticalSet (f : E → F) : Set E :=
  {x | ¬Surjective (fderiv ℝ f x)}
```
</details>

<div class="theorem-block" markdown>
<span class="badge badge--proved">Proved</span>
<span class="theorem-name">(criticalValues)</span>

**Definition.** The *critical values* of \(f\) are the image of the critical set: \(\operatorname{CritVal}(f) = f(\operatorname{Crit}(f))\).
</div>

<details>
<summary>Lean 4 statement --- <code>SardInfra.lean:81</code></summary>

```lean
def criticalValues (f : E → F) : Set F :=
  f '' criticalSet f
```
</details>

## Structural lemmas

<div class="theorem-block" markdown>
<span class="badge badge--proved">Proved</span>
<span class="theorem-name">(det_fderiv_eq_zero_of_not_surjective)</span>

**Lemma.** If \(L : E \to_L E\) is a continuous linear endomorphism that is not surjective, then \(\det L = 0\).
</div>

<details>
<summary>Lean 4 statement --- <code>SardInfra.lean:93</code></summary>

```lean
lemma det_fderiv_eq_zero_of_not_surjective (L : E →L[ℝ] E)
    (h : ¬Surjective L) : L.det = 0
```
</details>

<div class="theorem-block" markdown>
<span class="badge badge--proved">Proved</span>
<span class="theorem-name">(ContinuousLinearMap.surjective_iff_det_ne_zero)</span>

**Theorem.** A continuous linear endomorphism \(L : E \to_L E\) on a finite-dimensional space is surjective iff \(\det L \ne 0\):

$$L \text{ surjective} \;\iff\; \det L \ne 0.$$

</div>

<details>
<summary>Lean 4 statement --- <code>SardInfra.lean:101</code></summary>

```lean
theorem ContinuousLinearMap.surjective_iff_det_ne_zero
    (L : E →L[ℝ] E) : Surjective L ↔ L.det ≠ 0
```
</details>

<div class="theorem-block" markdown>
<span class="badge badge--proved">Proved</span>
<span class="theorem-name">(criticalSet_eq_det_zero)</span>

**Theorem.** The critical set coincides with the zero locus of the Jacobian determinant:
\(\operatorname{Crit}(f) = \{x \mid \det Df(x) = 0\}\).
</div>

<details>
<summary>Lean 4 statement --- <code>SardInfra.lean:117</code></summary>

```lean
theorem criticalSet_eq_det_zero (f : E → E) :
    criticalSet f = {x | (fderiv ℝ f x).det = 0}
```
</details>

<div class="theorem-block" markdown>
<span class="badge badge--proved">Proved</span>
<span class="theorem-name">(isClosed_criticalSet_of_contDiff)</span>

**Theorem.** If \(f : E \to E\) is \(C^\infty\), then \(\operatorname{Crit}(f)\) is closed.
</div>

<details>
<summary>Lean 4 statement --- <code>SardInfra.lean:123</code></summary>

```lean
theorem isClosed_criticalSet_of_contDiff (f : E → E)
    (hf : ContDiff ℝ ⊤ f) : IsClosed (criticalSet f)
```
</details>

## Equidimensional Sard

<div class="theorem-block" markdown>
<span class="badge badge--proved">Proved</span>
<span class="theorem-name">(sard_equidim)</span>

**Theorem (Sard, equidimensional).** Let \(E\) be a finite-dimensional real normed space with additive Haar measure \(\mu\). If \(f : E \to E\) is \(C^\infty\), then \(\mu(\operatorname{CritVal}(f)) = 0\).
</div>

The proof uses the Jacobian area formula: \(\mu(f(S)) \le \int_S |\det Df(x)|\,d\mu(x)\). On the critical set, \(\det Df(x) = 0\) identically, so the integral vanishes.

<details>
<summary>Lean 4 statement --- <code>SardInfra.lean:140</code></summary>

```lean
theorem sard_equidim (f : E → E) (hf : ContDiff ℝ ⊤ f)
    (μ : Measure E) [μ.IsAddHaarMeasure] :
    μ (criticalValues f) = 0
```
</details>

## Low-dimensional Sard

<div class="theorem-block" markdown>
<span class="badge badge--proved">Proved</span>
<span class="theorem-name">(sard_low_dim)</span>

**Theorem (Sard, low-dimensional).** If \(\dim_{\mathbb{R}} E < \dim_{\mathbb{R}} F\) and \(f : E \to F\) is \(C^\infty\), then \(\mu(\operatorname{CritVal}(f)) = 0\). In fact, the *entire* image \(f(E)\) has measure zero.
</div>

Smooth maps do not increase Hausdorff dimension: \(\dim_H(f(E)) \le \dim_{\mathbb{R}} E < \dim_{\mathbb{R}} F\). The Haar measure is absolutely continuous with respect to Hausdorff measure at dimension \(\dim F\), giving \(\mu(f(E)) = 0\).

<details>
<summary>Lean 4 statement --- <code>SardInfra.lean:184</code></summary>

```lean
theorem sard_low_dim (f : E → F) (hf : ContDiff ℝ ⊤ f)
    (hdim : finrank ℝ E < finrank ℝ F)
    (μ : Measure F) [μ.IsAddHaarMeasure] :
    μ (criticalValues f) = 0
```
</details>

## General equidimensional Sard

To handle \(f : E \to F\) with \(\dim E = \dim F\) (not just endomorphisms), we transport through a continuous linear equivalence.

<div class="theorem-block" markdown>
<span class="badge badge--proved">Proved</span>
<span class="theorem-name">(exists_continuousLinearEquiv_of_finrank_eq)</span>

**Theorem.** If \(\dim_{\mathbb{R}} E = \dim_{\mathbb{R}} F\), then there exists a continuous linear equivalence \(E \simeq_L F\).
</div>

<details>
<summary>Lean 4 statement --- <code>SardInfra.lean:225</code></summary>

```lean
theorem exists_continuousLinearEquiv_of_finrank_eq
    (h : finrank ℝ E = finrank ℝ F) : Nonempty (E ≃L[ℝ] F)
```
</details>

<div class="theorem-block" markdown>
<span class="badge badge--proved">Proved</span>
<span class="theorem-name">(criticalSet_comp_equiv)</span>

**Theorem.** Post-composition with an isomorphism preserves the critical set: \(\operatorname{Crit}(e \circ f) = \operatorname{Crit}(f)\).
</div>

<details>
<summary>Lean 4 statement --- <code>SardInfra.lean:232</code></summary>

```lean
theorem criticalSet_comp_equiv (f : E → F) (e : F ≃L[ℝ] E) :
    criticalSet (e ∘ f) = criticalSet f
```
</details>

<div class="theorem-block" markdown>
<span class="badge badge--proved">Proved</span>
<span class="theorem-name">(ContinuousLinearEquiv.symm_preimage_eq_image)</span>

**Theorem.** For a continuous linear equivalence \(e\) and a set \(S\), \(e^{-1}(S) = e(S)\).
</div>

<details>
<summary>Lean 4 statement --- <code>SardInfra.lean:252</code></summary>

```lean
theorem ContinuousLinearEquiv.symm_preimage_eq_image
    (e : E ≃L[ℝ] F) (S : Set E) :
    e.symm ⁻¹' S = e '' S
```
</details>

<div class="theorem-block" markdown>
<span class="badge badge--proved">Proved</span>
<span class="theorem-name">(map_continuousLinearEquiv_isAddHaarMeasure)</span>

**Instance.** If \(\mu\) is an additive Haar measure on \(F\) and \(e : E \simeq_L F\), then the pushforward is an additive Haar measure on \(E\).
</div>

<details>
<summary>Lean 4 statement --- <code>SardInfra.lean:261</code></summary>

```lean
instance map_continuousLinearEquiv_isAddHaarMeasure
    (e : E ≃L[ℝ] F) (μ : Measure F) [μ.IsAddHaarMeasure] :
    (Measure.map e.symm μ).IsAddHaarMeasure
```
</details>

<div class="theorem-block" markdown>
<span class="badge badge--proved">Proved</span>
<span class="theorem-name">(sard_equidim_general)</span>

**Theorem (Sard, equidimensional, general).** If \(\dim_{\mathbb{R}} E = \dim_{\mathbb{R}} F\) and \(f : E \to F\) is \(C^\infty\), then \(\mu(\operatorname{CritVal}(f)) = 0\).
</div>

The proof picks \(e : E \simeq_L F\), sets \(g = e^{-1} \circ f : E \to E\), applies `sard_equidim` to \(g\), and transfers back.

<details>
<summary>Lean 4 statement --- <code>SardInfra.lean:269</code></summary>

```lean
theorem sard_equidim_general (f : E → F) (hf : ContDiff ℝ ⊤ f)
    (hdim : finrank ℝ E = finrank ℝ F)
    (μ : Measure F) [μ.IsAddHaarMeasure] :
    μ (criticalValues f) = 0
```
</details>

## The axiom boundary

<div class="theorem-block" markdown>
<span class="badge badge--deferred">Deferred</span>
<span class="theorem-name">(sard_of_finrank_gt --- gate 3)</span>

**Deferred.** The high-dimensional case (\(\dim E > \dim F\)) requires the Morse--Sard induction: stratification by vanishing order of derivatives, Taylor estimates, and Whitney-type covering arguments. This will be axiomatized as a `SardInfra` typeclass carrying the single axiom that \(\mu(\operatorname{CritVal}(f)) = 0\) when \(\dim E > \dim F\) and \(f\) is sufficiently smooth.
</div>

The boundary is deliberate. The equidimensional and low-dimensional cases have clean proofs using existing Mathlib infrastructure. The high-dimensional case requires substantial new machinery that does not yet exist in Mathlib. Rather than axiomatizing the entire theorem, the formalization proves what it can and isolates the remaining obligation in a single, clearly scoped axiom.

## References

- Sard, A. (1942). "The measure of the critical values of differentiable maps." *Bull. Amer. Math. Soc.* 48(12), pp. 883--890.
- Mathlib: `MeasureTheory.addHaar_image_le_lintegral_abs_det_fderiv` (Jacobian area formula), `ContDiffOn.dimH_image_le` (Hausdorff dimension bound).
