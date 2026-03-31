# Delay Embedding & Orbit Separation

The delay embedding is the central construction of Takens (1981): given a
dynamical system \(f : X \to X\) and a scalar observation \(\alpha : X \to \mathbb{R}\),
the delay embedding of window length \(k\) maps each state \(x\) to the vector
of consecutive observations along its orbit,

\[
\Phi_{f,\alpha,k}(x) \;=\; \bigl(\alpha(x),\; \alpha(f(x)),\; \dots,\; \alpha(f^{k-1}(x))\bigr) \;\in\; \mathbb{R}^k.
\]

The headline result of this module is an exact characterization: the delay
embedding is injective if and only if the observation function separates
all pairs of orbit segments of length \(k\). This discrete algebraic equivalence
is the foundation on which the rest of Route B is built.

## Core definitions

<div class="theorem-block" markdown>
<span class="badge badge--proved">Proved</span>
<span class="theorem-name">(delayEmbedding)</span>

**Definition.** The *delay embedding* of window length \(k\) for dynamics \(f : X \to X\) and observation \(\alpha : X \to \mathbb{R}\) is the map
\[
\Phi_{f,\alpha,k} : X \to \mathbb{R}^k, \qquad \Phi_{f,\alpha,k}(x)(i) = \alpha(f^i(x)), \quad 0 \le i < k.
\]
</div>

<details>
<summary>Lean 4 statement --- <code>DelayWindow.lean:56</code></summary>

```lean
def delayEmbedding (f : X → X) (α : X → ℝ) (k : ℕ) (x : X) : Fin k → ℝ :=
  fun i => α (f^[i.val] x)
```
</details>

<div class="theorem-block" markdown>
<span class="badge badge--proved">Proved</span>
<span class="theorem-name">(SeparatesOrbits)</span>

**Definition.** An observation \(\alpha\) *separates \(f\)-orbits of length \(k\)* if, for all \(x, y \in X\),
\[
\bigl(\forall\, 0 \le i < k,\; \alpha(f^i(x)) = \alpha(f^i(y))\bigr) \;\Longrightarrow\; x = y.
\]
</div>

<details>
<summary>Lean 4 statement --- <code>DelayWindow.lean:71</code></summary>

```lean
def SeparatesOrbits (f : X → X) (α : X → ℝ) (k : ℕ) : Prop :=
  ∀ x y : X,
    (∀ i : Fin k, α (f^[i.val] x) = α (f^[i.val] y)) → x = y
```
</details>

<div class="theorem-block" markdown>
<span class="badge badge--proved">Proved</span>
<span class="theorem-name">(WindowDistinct)</span>

**Definition.** A state \(x\) has a *tie-free delay window* of length \(k\) if the values \(\alpha(f^i(x))\) are pairwise distinct for \(0 \le i < k\). Equivalently, the delay embedding at \(x\) is injective as a function \(\{0, \dots, k-1\} \to \mathbb{R}\).
</div>

<details>
<summary>Lean 4 statement --- <code>DelayWindow.lean:123</code></summary>

```lean
def WindowDistinct (f : X → X) (α : X → ℝ) (k : ℕ) (x : X) : Prop :=
  Injective (delayEmbedding f α k x)
```
</details>

## Headline theorem

<div class="theorem-block" markdown>
<span class="badge badge--proved">Proved</span>
<span class="theorem-name">(delayEmbedding_injective_iff_separatesOrbits)</span>

**Theorem.** The delay embedding \(\Phi_{f,\alpha,k}\) is injective if and only if \(\alpha\) separates \(f\)-orbits of length \(k\):
\[
\Phi_{f,\alpha,k} \text{ injective} \;\iff\; \operatorname{SeparatesOrbits}(f, \alpha, k).
\]
</div>

<details>
<summary>Lean 4 statement --- <code>DelayWindow.lean:77</code></summary>

```lean
theorem delayEmbedding_injective_iff_separatesOrbits
    (f : X → X) (α : X → ℝ) (k : ℕ) :
    Injective (delayEmbedding f α k) ↔ SeparatesOrbits f α k
```
</details>

This is the discrete algebraic core of Takens (1981). The forward direction
is immediate (injectivity of the composite implies agreement of inputs); the
reverse direction unfolds the definition and applies orbit separation pointwise.

## Continuity and cardinality

<div class="theorem-block" markdown>
<span class="badge badge--proved">Proved</span>
<span class="theorem-name">(delayEmbedding_continuous)</span>

**Theorem.** If \(f\) and \(\alpha\) are continuous, then \(\Phi_{f,\alpha,k}\) is continuous (with the product topology on \(\mathbb{R}^k\)).
</div>

<details>
<summary>Lean 4 statement --- <code>DelayWindow.lean:182</code></summary>

```lean
theorem delayEmbedding_continuous [TopologicalSpace X]
    {f : X → X} {α : X → ℝ} (hf : Continuous f) (hα : Continuous α)
    (k : ℕ) :
    Continuous (delayEmbedding f α k)
```
</details>

<div class="theorem-block" markdown>
<span class="badge badge--proved">Proved</span>
<span class="theorem-name">(delayEmbedding_image_card_le)</span>

**Theorem.** On a finite type \(X\), the number of distinct delay windows is at most \(|X|\):
\[
\bigl|\{\Phi_{f,\alpha,k}(x) : x \in X\}\bigr| \;\le\; |X|.
\]
</div>

<details>
<summary>Lean 4 statement --- <code>DelayWindow.lean:130</code></summary>

```lean
theorem delayEmbedding_image_card_le [Fintype X]
    (f : X → X) (α : X → ℝ) (k : ℕ) :
    (Finset.univ.image (delayEmbedding f α k)).card ≤ Fintype.card X
```
</details>

<div class="theorem-block" markdown>
<span class="badge badge--proved">Proved</span>
<span class="theorem-name">(delayEmbedding_image_card_of_injective)</span>

**Theorem.** If \(\Phi_{f,\alpha,k}\) is injective on a finite type, the image has exactly \(|X|\) elements:
\[
\Phi_{f,\alpha,k} \text{ injective} \;\Longrightarrow\; \bigl|\{\Phi_{f,\alpha,k}(x) : x \in X\}\bigr| = |X|.
\]
</div>

<details>
<summary>Lean 4 statement --- <code>DelayWindow.lean:138</code></summary>

```lean
theorem delayEmbedding_image_card_of_injective [Fintype X]
    (f : X → X) (α : X → ℝ) (k : ℕ)
    (h : Injective (delayEmbedding f α k)) :
    (Finset.univ.image (delayEmbedding f α k)).card = Fintype.card X
```
</details>

## Period bridge lemmas

The following results from `IteratePeriod.lean` connect the orbit separation
framework to Mathlib's `Function.minimalPeriod` API, bridging the generic delay
embedding characterization to concrete period bounds on finite types.

<div class="theorem-block" markdown>
<span class="badge badge--proved">Proved</span>
<span class="theorem-name">(separatesOrbits_of_injective)</span>

**Theorem.** If \(\alpha\) is injective, then \(\alpha\) separates \(f\)-orbits of any length \(k \ge 1\).
</div>

<details>
<summary>Lean 4 statement --- <code>IteratePeriod.lean:53</code></summary>

```lean
theorem separatesOrbits_of_injective {f : X → X} {α : X → ℝ}
    (hα : Injective α) {k : ℕ} (hk : 0 < k) :
    SeparatesOrbits f α k
```
</details>

<div class="theorem-block" markdown>
<span class="badge badge--proved">Proved</span>
<span class="theorem-name">(windowDistinct_of_injective_of_le_minimalPeriod)</span>

**Theorem.** If \(\alpha\) is injective and \(k \le p(x)\), where \(p(x)\) is the minimal period of \(x\) under \(f\), then the delay window at \(x\) is tie-free:
\[
\alpha \text{ injective},\; k \le \operatorname{minPeriod}_f(x) \;\Longrightarrow\; \operatorname{WindowDistinct}(f, \alpha, k, x).
\]
This is the key precondition for ordinal pattern extraction.
</div>

<details>
<summary>Lean 4 statement --- <code>IteratePeriod.lean:64</code></summary>

```lean
theorem windowDistinct_of_injective_of_le_minimalPeriod
    {f : X → X} {α : X → ℝ}
    (hα : Injective α) {k : ℕ} {x : X}
    (hk : k ≤ minimalPeriod f x) :
    WindowDistinct f α k x
```
</details>

<div class="theorem-block" markdown>
<span class="badge badge--proved">Proved</span>
<span class="theorem-name">(isPeriodicPt_of_injective_iterate_eq)</span>

**Theorem.** If \(f\) is injective and \(f^i(x) = f^j(x)\) with \(i \ne j\), then \(x\) is a periodic point.
</div>

<details>
<summary>Lean 4 statement --- <code>IteratePeriod.lean:81</code></summary>

```lean
theorem isPeriodicPt_of_injective_iterate_eq
    {f : X → X} (hf : Injective f) {x : X} {i j : ℕ}
    (hij : i ≠ j) (h : f^[i] x = f^[j] x) :
    ∃ p, 0 < p ∧ f^[p] x = x
```
</details>

<div class="theorem-block" markdown>
<span class="badge badge--proved">Proved</span>
<span class="theorem-name">(windowDistinct_of_injective_orbit)</span>

**Theorem.** If \(\alpha\) is injective and the orbit segment \((f^0(x), \dots, f^{k-1}(x))\) has no repeated points, the delay window is tie-free.
</div>

<details>
<summary>Lean 4 statement --- <code>IteratePeriod.lean:95</code></summary>

```lean
theorem windowDistinct_of_injective_orbit
    {f : X → X} {α : X → ℝ} (hα : Injective α) {k : ℕ} {x : X}
    (h : ∀ i j : Fin k, f^[i.val] x = f^[j.val] x → i = j) :
    WindowDistinct f α k x
```
</details>

## Mathematical context

The delay embedding theorem of Takens (1981) asserts that, generically,
the delay coordinate map is an embedding of the attractor into
\(\mathbb{R}^k\) for sufficiently large \(k\). The results formalized here
capture the discrete algebraic skeleton: the exact equivalence
between injectivity of \(\Phi_{f,\alpha,k}\) and orbit separation, together with
the period-based conditions under which delay windows are tie-free (a necessary
prerequisite for ordinal pattern extraction).

The smooth embedding theorem (compact + injective implies closed embedding
and homeomorphism onto image) is formalized separately in Route A
(`SmoothTakens.lean`). The two routes are independent proof trees with
no shared definitions.

!!! tip "Connection to navi-SAD"
    The delay embedding is the theoretical foundation of navi-SAD's attractor reconstruction pipeline. See [Formal Backing for navi-SAD](../bridge/navi-sad.md).
