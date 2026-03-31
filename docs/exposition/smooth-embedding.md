# Smooth Embedding Chain

Route A of the formalization addresses the *smooth* side of Takens' delay embedding theorem (Takens, 1981): given a dynamical system \(T : X \to X\) and an observation function \(h : X \to \mathbb{R}\), the delay coordinate map

\[
\Phi_{T,h,n} : X \longrightarrow \mathbb{R}^n, \qquad x \longmapsto \bigl(h(x),\, h(Tx),\, \dots,\, h(T^{n-1}x)\bigr)
\]

is a topological embedding under appropriate hypotheses. This page documents the **embedding chain**: the sequence of results that, starting from the bare definition, establishes continuity, then promotes injectivity on a compact space to a closed embedding, and finally constructs a homeomorphism onto the image.

The most notable structural feature of this file is that **it is entirely axiom-free**. `SmoothTakens.lean` does not import `SardInfra` or any axiomatized infrastructure. Every result on this page is a closed proof within Lean 4 + Mathlib, with no `sorry` and no custom axioms. The genericity half of the smooth Takens theorem (showing that the "good" observation functions are generic) will eventually depend on Sard's theorem; the embedding half documented here stands on its own.

## Definition

<div class="theorem-block">
<span class="badge badge--axiom-free">Axiom-free</span>
<span class="theorem-name">(smoothDelayMap)</span>

**Definition.** Let \(X\) be a topological space, \(T : X \to X\) a self-map, \(h : X \to \mathbb{R}\) an observation function, and \(n \in \mathbb{N}\). The *smooth delay map* is

\[
\operatorname{smoothDelayMap}(T, h, n)(x) \;=\; \bigl(i \mapsto h(T^i(x))\bigr) \;\in\; \mathbb{R}^n.
\]
</div>

<details>
<summary>Lean 4 statement --- <code>SmoothTakens.lean:56</code></summary>

```lean
def smoothDelayMap (T : X → X) (h : X → ℝ) (n : ℕ) : X → (Fin n → ℝ) :=
  fun x i => h (T^[i] x)
```
</details>

## Continuity

<div class="theorem-block">
<span class="badge badge--axiom-free">Axiom-free</span>
<span class="theorem-name">(smoothDelayMap_continuous)</span>

**Theorem.** If \(T : X \to X\) and \(h : X \to \mathbb{R}\) are continuous, then \(\operatorname{smoothDelayMap}(T, h, n)\) is continuous for every \(n\).
</div>

The proof applies `continuous_pi`: it suffices to show each coordinate \(i \mapsto h \circ T^i\) is continuous. This follows because \(T^i\) is continuous (by induction on the iterate) and \(h\) is continuous.

<details>
<summary>Lean 4 statement --- <code>SmoothTakens.lean:61</code></summary>

```lean
theorem smoothDelayMap_continuous
    {T : X → X} {h : X → ℝ} (hT : Continuous T) (hh : Continuous h)
    {n : ℕ} :
    Continuous (smoothDelayMap T h n)
```
</details>

## Closed embedding

<div class="theorem-block">
<span class="badge badge--axiom-free">Axiom-free</span>
<span class="theorem-name">(smoothDelayMap_isClosedEmbedding)</span>

**Theorem.** If \(X\) is compact, \(T\) and \(h\) are continuous, and \(\operatorname{smoothDelayMap}(T, h, n)\) is injective, then it is a closed embedding into \(\mathbb{R}^n\).
</div>

This is the key step. The codomain \(\operatorname{Fin}\, n \to \mathbb{R}\) is Hausdorff (it is a real topological vector space), and the domain is compact. A continuous injection from a compact space to a Hausdorff space is automatically a closed embedding.

<details>
<summary>Lean 4 statement --- <code>SmoothTakens.lean:73</code></summary>

```lean
theorem smoothDelayMap_isClosedEmbedding [CompactSpace X]
    {T : X → X} {h : X → ℝ} (hT : Continuous T) (hh : Continuous h)
    {n : ℕ} (hinj : Injective (smoothDelayMap T h n)) :
    IsClosedEmbedding (smoothDelayMap T h n)
```
</details>

## Embedding

<div class="theorem-block">
<span class="badge badge--axiom-free">Axiom-free</span>
<span class="theorem-name">(smoothDelayMap_isEmbedding)</span>

**Theorem.** Under the same hypotheses (compact domain, continuous \(T\) and \(h\), injective delay map), \(\operatorname{smoothDelayMap}(T, h, n)\) is a topological embedding.
</div>

This is an immediate corollary: every closed embedding is an embedding.

<details>
<summary>Lean 4 statement --- <code>SmoothTakens.lean:81</code></summary>

```lean
theorem smoothDelayMap_isEmbedding [CompactSpace X]
    {T : X → X} {h : X → ℝ} (hT : Continuous T) (hh : Continuous h)
    {n : ℕ} (hinj : Injective (smoothDelayMap T h n)) :
    IsEmbedding (smoothDelayMap T h n)
```
</details>

## Homeomorphism onto image

<div class="theorem-block">
<span class="badge badge--axiom-free">Axiom-free</span>
<span class="theorem-name">(smoothDelayMap_rangeHomeomorph)</span>

**Definition.** Under the same hypotheses, the range factorization of the smooth delay map is a homeomorphism

\[
X \;\cong_{\mathrm{top}}\; \operatorname{range}\bigl(\operatorname{smoothDelayMap}(T, h, n)\bigr).
\]
</div>

This is the terminal result of the embedding chain. The construction uses `Equiv.ofInjective` to build a bijection onto the range, then lifts it to a homeomorphism via the inducing property of the closed embedding. The result is a concrete `Homeomorph` (`\cong_\top`), not merely an abstract existence statement.

<details>
<summary>Lean 4 statement --- <code>SmoothTakens.lean:89</code></summary>

```lean
def smoothDelayMap_rangeHomeomorph [CompactSpace X]
    {T : X → X} {h : X → ℝ} (hT : Continuous T) (hh : Continuous h)
    {n : ℕ} (hinj : Injective (smoothDelayMap T h n)) :
    X ≃ₜ range (smoothDelayMap T h n)
```
</details>

## What is not here

The *genericity* half of Takens' theorem --- that the set of observation functions \(h\) making the delay map injective is *generic* (residual in the \(C^2\) topology) --- requires Sard's theorem and parametric transversality. That argument will eventually import `SardInfra` (see [Sard Infrastructure](sard-infrastructure.md)). The embedding chain documented here is the half that does not need measure theory, and it is complete.
