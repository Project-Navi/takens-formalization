# Ordinal Compression

The ordinal pattern of a finite real-valued sequence extracts only the
*relative ordering* of its entries, discarding all magnitude information.
Given an injective function \(f : \{0, \dots, d-1\} \to \mathbb{R}\), its ordinal
pattern is the unique permutation \(\sigma \in S_d\) such that
\(f \circ \sigma\) is strictly increasing:

$$f(\sigma(0)) < f(\sigma(1)) < \cdots < f(\sigma(d-1)).$$

This construction, due to Bandt and Pompe (2002), is the basis of permutation
entropy and a wide family of complexity measures for time series. Composing
ordinal pattern extraction with the delay embedding yields the *ordinal delay
map* --- a lossy compression of delay windows that is invariant under monotone
observation transforms and whose codomain has size at most \(d!\).

## Ordinal pattern: definitions and properties

<div class="theorem-block" markdown>
<span class="badge badge--proved">Proved</span>
<span class="theorem-name">(IsOrdinalPatternOf)</span>

**Definition.** A permutation \(\sigma \in S_d\) is the *ordinal pattern of* \(f : \{0,\dots,d-1\} \to \mathbb{R}\) if \(f \circ \sigma\) is strictly monotone:

$$\operatorname{IsOrdinalPatternOf}(\sigma, f) \;\iff\; f(\sigma(i)) < f(\sigma(j)) \text{ for all } i < j.$$

</div>

<details>
<summary>Lean 4 statement --- <code>OrdinalPattern.lean:59</code></summary>

```lean
def IsOrdinalPatternOf (σ : Equiv.Perm (Fin d)) (f : Fin d → ℝ) : Prop :=
  StrictMono (f ∘ σ)
```
</details>

<div class="theorem-block" markdown>
<span class="badge badge--proved">Proved</span>
<span class="theorem-name">(ordinalPattern)</span>

**Definition.** For an injective \(f : \{0,\dots,d-1\} \to \mathbb{R}\), the *ordinal pattern* \(\pi(f)\) is the unique permutation \(\sigma \in S_d\) such that \(f \circ \sigma\) is strictly increasing.
</div>

<details>
<summary>Lean 4 statement --- <code>OrdinalPattern.lean:105</code></summary>

```lean
noncomputable def ordinalPattern (f : Fin d → ℝ) (hf : Injective f) :
    Equiv.Perm (Fin d) :=
  (ordinalPattern_exists_unique f hf).choose
```
</details>

<div class="theorem-block" markdown>
<span class="badge badge--proved">Proved</span>
<span class="theorem-name">(ordinalPattern_exists_unique)</span>

**Theorem.** For any injective \(f : \{0,\dots,d-1\} \to \mathbb{R}\), there exists a unique permutation \(\sigma \in S_d\) such that \(f \circ \sigma\) is strictly monotone:

$$\exists!\, \sigma \in S_d, \quad \operatorname{IsOrdinalPatternOf}(\sigma, f).$$

</div>

<details>
<summary>Lean 4 statement --- <code>OrdinalPattern.lean:97</code></summary>

```lean
theorem ordinalPattern_exists_unique (f : Fin d → ℝ) (hf : Injective f) :
    ∃! σ : Equiv.Perm (Fin d), IsOrdinalPatternOf σ f
```
</details>

Existence is witnessed by `Tuple.sort` from Mathlib; uniqueness follows because
two permutations that both sort the same injective function must agree on every
input.

<div class="theorem-block" markdown>
<span class="badge badge--proved">Proved</span>
<span class="theorem-name">(isOrdinalPatternOf_comp_strictMono)</span>

**Theorem (Monotone invariance).** If \(\sigma\) is the ordinal pattern of \(f\) and \(g : \mathbb{R} \to \mathbb{R}\) is strictly monotone, then \(\sigma\) is also the ordinal pattern of \(g \circ f\):

$$\operatorname{IsOrdinalPatternOf}(\sigma, f) \;\wedge\; g \text{ strictly monotone} \;\Longrightarrow\; \operatorname{IsOrdinalPatternOf}(\sigma, g \circ f).$$

Ordinal patterns depend only on relative ordering, not on the scale or shape of the observation function.
</div>

<details>
<summary>Lean 4 statement --- <code>OrdinalPattern.lean:64</code></summary>

```lean
theorem isOrdinalPatternOf_comp_strictMono {σ : Equiv.Perm (Fin d)}
    {f : Fin d → ℝ} {g : ℝ → ℝ} (hσ : IsOrdinalPatternOf σ f)
    (hg : StrictMono g) :
    IsOrdinalPatternOf σ (g ∘ f)
```
</details>

<div class="theorem-block" markdown>
<span class="badge badge--proved">Proved</span>
<span class="theorem-name">(ordinalPattern_surjective)</span>

**Theorem (Surjectivity).** Every permutation \(\sigma \in S_d\) is realizable as the ordinal pattern of some injective function:

$$\forall\, \sigma \in S_d, \quad \exists\, f : \{0,\dots,d-1\} \hookrightarrow \mathbb{R}, \quad \pi(f) = \sigma.$$

</div>

<details>
<summary>Lean 4 statement --- <code>OrdinalPattern.lean:131</code></summary>

```lean
theorem ordinalPattern_surjective (σ : Equiv.Perm (Fin d)) :
    ∃ (f : Fin d → ℝ), ∃ (hf : Injective f), ordinalPattern f hf = σ
```
</details>

## The ordinal delay map

Composing the delay embedding \(\Phi_{f,\alpha,k}\) with ordinal pattern extraction
yields the *ordinal delay map*, a compression from states to permutations.
It is defined on the subtype of states with tie-free windows
(\(\operatorname{WindowDistinct}\)), since ordinal pattern extraction requires
injectivity of the input function.

<div class="theorem-block" markdown>
<span class="badge badge--proved">Proved</span>
<span class="theorem-name">(ordinalDelayMap)</span>

**Definition.** The *ordinal delay map* of window length \(k\) sends each state \(x\) (with tie-free window) to the ordinal pattern of its delay vector:

$$\Pi_{f,\alpha,k} : \{x \in X \mid \operatorname{WindowDistinct}(f,\alpha,k,x)\} \;\to\; S_k, \qquad \Pi_{f,\alpha,k}(x) = \pi\bigl(\Phi_{f,\alpha,k}(x)\bigr).$$

</div>

<details>
<summary>Lean 4 statement --- <code>OrdinalTakens.lean:55</code></summary>

```lean
noncomputable def ordinalDelayMap (f : X → X) (α : X → ℝ) (k : ℕ)
    (x : { x : X // WindowDistinct f α k x }) : Equiv.Perm (Fin k) :=
  ordinalPattern (delayEmbedding f α k x.val) x.prop
```
</details>

<div class="theorem-block" markdown>
<span class="badge badge--proved">Proved</span>
<span class="theorem-name">(ordinalDelayMap_monotone_invariant)</span>

**Theorem (Monotone invariance of the ordinal delay map).** If \(g : \mathbb{R} \to \mathbb{R}\) is strictly monotone, then replacing \(\alpha\) by \(g \circ \alpha\) does not change the ordinal delay map:

$$g \text{ strictly monotone} \;\Longrightarrow\; \Pi_{f,\, g \circ \alpha,\, k}(x) \;=\; \Pi_{f,\alpha,k}(x).$$

This is the formal justification for the robustness of permutation entropy to monotone signal transformations.
</div>

<details>
<summary>Lean 4 statement --- <code>OrdinalTakens.lean:65</code></summary>

```lean
theorem ordinalDelayMap_monotone_invariant {f : X → X} {α : X → ℝ}
    {g : ℝ → ℝ} (hg : StrictMono g) {k : ℕ}
    (x : { x : X // WindowDistinct f α k x })
    (hgx : WindowDistinct f (g ∘ α) k x.val) :
    ordinalDelayMap f (g ∘ α) k ⟨x.val, hgx⟩ =
      ordinalDelayMap f α k x
```
</details>

<div class="theorem-block" markdown>
<span class="badge badge--proved">Proved</span>
<span class="theorem-name">(ordinalDelayMap_eq_of_order_eq)</span>

**Theorem (Order characterization).** Two states with the same relative ordering in their delay windows receive the same ordinal pattern.
</div>

<details>
<summary>Lean 4 statement --- <code>OrdinalTakens.lean:79</code></summary>

```lean
theorem ordinalDelayMap_eq_of_order_eq {f : X → X} {α : X → ℝ} {k : ℕ}
    (x y : { x : X // WindowDistinct f α k x })
    (h : ∀ i j : Fin k,
      delayEmbedding f α k x.val i < delayEmbedding f α k x.val j ↔
      delayEmbedding f α k y.val i < delayEmbedding f α k y.val j) :
    ordinalDelayMap f α k x = ordinalDelayMap f α k y
```
</details>

## Observed patterns and counting bounds

Given an orbit of length \(N\) and a window size \(d\), the *observed patterns*
are the ordinal patterns encountered along the orbit. Three independent
upper bounds constrain the size of this set.

<div class="theorem-block" markdown>
<span class="badge badge--proved">Proved</span>
<span class="theorem-name">(observedPatterns)</span>

**Definition.** The *observed patterns* along an orbit of length \(N\) with window size \(d\):

$$\operatorname{ObsPatterns}(f, \alpha, d, x, N) \;=\; \bigl\{\pi\bigl(\alpha(f^{t}(x)),\, \dots,\, \alpha(f^{t+d-1}(x))\bigr) : 0 \le t < N \bigr\} \;\subseteq\; S_d.$$

</div>

<details>
<summary>Lean 4 statement --- <code>OrdinalTakens.lean:98</code></summary>

```lean
noncomputable def observedPatterns
    (f : X → X) (α : X → ℝ) (d : ℕ) (x : X) (N : ℕ) :
    Finset (Equiv.Perm (Fin d)) :=
  (Finset.range N).image (fun t =>
    Tuple.sort (fun i : Fin d => α (f^[t + i.val] x)))
```
</details>

<div class="theorem-block" markdown>
<span class="badge badge--proved">Proved</span>
<span class="theorem-name">(card_observedPatterns_le_factorial)</span>

**Theorem (Factorial bound).** \(\bigl|\operatorname{ObsPatterns}(f, \alpha, d, x, N)\bigr| \;\le\; d!\)
</div>

<details>
<summary>Lean 4 statement --- <code>OrdinalTakens.lean:105</code></summary>

```lean
theorem card_observedPatterns_le_factorial
    (f : X → X) (α : X → ℝ) (d : ℕ) (x : X) (N : ℕ) :
    (observedPatterns f α d x N).card ≤ d.factorial
```
</details>

<div class="theorem-block" markdown>
<span class="badge badge--proved">Proved</span>
<span class="theorem-name">(card_observedPatterns_le_length)</span>

**Theorem (Length bound).** \(\bigl|\operatorname{ObsPatterns}(f, \alpha, d, x, N)\bigr| \;\le\; N.\)
</div>

<details>
<summary>Lean 4 statement --- <code>OrdinalTakens.lean:113</code></summary>

```lean
theorem card_observedPatterns_le_length
    (f : X → X) (α : X → ℝ) (d : ℕ) (x : X) (N : ℕ) :
    (observedPatterns f α d x N).card ≤ N
```
</details>

<div class="theorem-block" markdown>
<span class="badge badge--proved">Proved</span>
<span class="theorem-name">(card_observedPatterns_le_period)</span>

**Theorem (Period bound).** On a periodic orbit, the number of distinct ordinal patterns is at most the minimal period:

$$x \in \operatorname{PeriodicPts}(f) \;\Longrightarrow\; \bigl|\operatorname{ObsPatterns}(f, \alpha, d, x, N)\bigr| \;\le\; \operatorname{minPeriod}_f(x).$$

</div>

<details>
<summary>Lean 4 statement --- <code>OrdinalTakens.lean:121</code></summary>

```lean
theorem card_observedPatterns_le_period
    (f : X → X) (α : X → ℝ) (d : ℕ) (x : X) (N : ℕ)
    (hx : x ∈ Function.periodicPts f) :
    (observedPatterns f α d x N).card ≤ Function.minimalPeriod f x
```
</details>

## Mathematical context

The three counting bounds give complementary constraints on the complexity of
ordinal dynamics:

| Bound | Source | Tight when |
|-------|--------|------------|
| \(\le d!\) | Codomain of \(S_d\) | Full permutation complexity (chaotic regime) |
| \(\le N\) | Pigeonhole on orbit length | Short transients |
| \(\le p(x)\) | Periodicity | Low-period attractors |

The *permutation entropy* of Bandt and Pompe (2002) is defined as
$$H_d(f, \alpha, x) \;=\; -\sum_{\sigma \in S_d} p_\sigma \log p_\sigma,$$
where \(p_\sigma\) is the relative frequency of pattern \(\sigma\) along the orbit.
The factorial bound gives the maximum entropy \(\log(d!)\); the period bound
shows that periodic orbits have entropy at most \(\log(p(x))\), independent
of orbit length.

The monotone invariance theorem is the formal justification for a key practical
property: permutation entropy is robust to any strictly monotone recalibration
of the observation function, making it well-suited to real-world signals where
sensor nonlinearity is present but monotone.

!!! tip "Connection to navi-SAD"
    The ordinal delay map formalizes the methodology behind navi-SAD's permutation entropy pipeline: per-head SAD trajectories are treated as delay-coordinate embeddings, and complexity is measured via the observed ordinal pattern distribution. See [Formal Backing for navi-SAD](../bridge/navi-sad.md).
