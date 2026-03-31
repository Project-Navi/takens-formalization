# Beyond Takens: Coincidence Length

In his landmark 1981 paper, Takens proved that for a compact manifold \(M\) of dimension \(m\), the delay coordinate map

\[
\Phi_{(\varphi, y)}(x) = \bigl(y(x),\; y(\varphi(x)),\; \ldots,\; y(\varphi^{2m}(x))\bigr)
\]

is an embedding for **generic** pairs \((\varphi, y)\) in the \(C^2\) topology --- that is, for a residual set (in the sense of Baire category) of diffeomorphisms \(\varphi : M \to M\) and observations \(y : M \to \mathbb{R}\).

This is a powerful existence result: it guarantees that *almost every* smooth observation function reconstructs the state space faithfully, provided the window length exceeds \(2m\). But it says nothing about what happens when the observation is **not** generic. Given a *specific* observation \(\alpha : X \to \mathbb{R}\) --- possibly non-injective, possibly coarse, possibly arising from a physical sensor with limited resolution --- can it still separate states via delay coordinates? If so, how long must the window be?

Takens' theorem is silent on this question. The coincidence length fills the gap.

## Coincidence length

Given a dynamical system \(f : X \to X\) and an observation \(\alpha : X \to \mathbb{R}\), two distinct states \(x \neq y\) may produce identical observations for several iterates before finally disagreeing. The **coincidence length** measures exactly how long two orbits look identical through the lens of \(\alpha\).

<div class="theorem-block">
<span class="badge badge--novel">Novel</span>
<span class="theorem-name">(coincidenceLength)</span>

**Definition.** Let \(f : X \to X\) and \(\alpha : X \to \mathbb{R}\). The *coincidence length* of two states \(x, y \in X\) is

\[
\mathrm{coinc}(x, y) \;=\; \begin{cases} \min\bigl\{\, i \in \mathbb{N} \;\big|\; \alpha(f^i(x)) \neq \alpha(f^i(y)) \,\bigr\} & \text{if such } i \text{ exists,} \\[4pt] \infty & \text{otherwise.} \end{cases}
\]

The coincidence length takes values in \(\mathbb{N}_\infty = \mathbb{N} \cup \{\infty\}\). It is finite for a pair \((x, y)\) precisely when the observation \(\alpha\) eventually distinguishes the orbits of \(x\) and \(y\).
</div>

<details>
<summary>Lean 4 statement --- <code>DelayWindow.lean:150</code></summary>

```lean
noncomputable def coincidenceLength (f : X → X) (α : X → ℝ)
    (x y : X) : ℕ∞ :=
  open Classical in
  if h : ∃ i : ℕ, α (f^[i] x) ≠ α (f^[i] y) then ↑(Nat.find h) else ⊤
```

</details>

Observe that \(\mathrm{coinc}(x, y) = 0\) means \(\alpha\) itself already distinguishes \(x\) from \(y\) (without any iteration). If \(\mathrm{coinc}(x, y) = n\), then the observation sequences agree on their first \(n\) terms but differ at step \(n\): the pair is "invisible" to any delay window of length \(\leq n\), but a window of length \(n + 1\) separates them.

The case \(\mathrm{coinc}(x, y) = \infty\) is the pathological one: the observation \(\alpha\) *never* distinguishes \(x\) from \(y\), no matter how long we observe. No delay window of any finite length can separate such a pair.

## The separating window theorem

The coincidence length leads directly to a sharp characterization of when a non-injective observation can nevertheless produce an injective delay embedding.

Recall that the delay embedding of window length \(k\) is defined as

\[
\Phi_k(x) = \bigl(\alpha(x),\; \alpha(f(x)),\; \ldots,\; \alpha(f^{k-1}(x))\bigr) \in \mathbb{R}^k,
\]

and we say \(\alpha\) **separates \(f\)-orbits of length \(k\)** if \(\Phi_k\) is injective: whenever \(\alpha(f^i(x)) = \alpha(f^i(y))\) for all \(0 \leq i < k\), then \(x = y\).

<div class="theorem-block">
<span class="badge badge--novel">Novel</span>
<span class="theorem-name">(exists_separatingWindow_iff)</span>

**Theorem.** Let \(X\) be a finite type, \(f : X \to X\), and \(\alpha : X \to \mathbb{R}\). Then the following are equivalent:

1. There exists a window length \(k \in \mathbb{N}\) such that \(\alpha\) separates \(f\)-orbits of length \(k\).
2. For every pair of distinct states \(x \neq y\), there exists \(i \in \mathbb{N}\) such that \(\alpha(f^i(x)) \neq \alpha(f^i(y))\).

Equivalently, in terms of the coincidence length:

\[
\bigl(\exists\, k.\; \Phi_k \text{ is injective}\bigr) \;\iff\; \bigl(\forall\, x \neq y.\; \mathrm{coinc}(x, y) < \infty\bigr).
\]

Moreover, when these conditions hold, the witness \(k\) is constructed explicitly as

\[
k \;=\; 1 + \max_{x, y \in X}\, \mathrm{coinc}(x, y),
\]

the supremum of all pairwise coincidence lengths, plus one.
</div>

<details>
<summary>Lean 4 statement --- <code>DelayWindow.lean:159</code></summary>

```lean
theorem exists_separatingWindow_iff (f : X → X) (α : X → ℝ)
    (hfin : Fintype X) :
    (∃ k, SeparatesOrbits f α k) ↔
      ∀ x y, x ≠ y → ∃ i : ℕ, α (f^[i] x) ≠ α (f^[i] y)
```

</details>

The proof of the reverse direction (2 implies 1) uses finiteness of \(X\) in an essential way: the choice function provides, for each distinct pair \((x, y)\), a witness index \(i_{x,y}\) at which their observations diverge. Because \(X\) is finite, the double supremum \(\sup_{x \in X} \sup_{y \in X} i_{x,y}\) is a well-defined natural number, and the window length \(k = 1 + \sup_{x,y} i_{x,y}\) suffices to separate all pairs simultaneously.

## Mathematical significance

**Filling a structural gap.** Takens' theorem is a *genericity* result: it tells us that most observations work, but nothing about which specific ones do. The separating window theorem provides a *pointwise* criterion. Given a concrete observation \(\alpha\) --- one that may fail to be injective, may fail to be smooth, may not belong to any residual set --- the theorem gives a necessary and sufficient condition for it to admit a separating delay window, and constructs the minimal sufficient window length when one exists.

**The role of finiteness.** The theorem requires \(X\) to be finite. This is not a limitation but a feature: finite state spaces are the natural setting for symbolic dynamics, computational models, and any system analyzed from discrete time-series data. On infinite state spaces the supremum over pairs may not exist, and indeed the equivalence fails without some compactness or finiteness hypothesis.

**A computable obstruction.** The condition \(\mathrm{coinc}(x, y) = \infty\) identifies precisely the obstruction to delay-coordinate reconstruction: a pair of states that are *observationally indistinguishable* under \(\alpha\) at every time step. When \(X\) is finite, checking the right-hand side is decidable --- one can enumerate all distinct pairs and verify eventual disagreement. This makes the theorem not just a classification result but a *diagnostic tool* for assessing whether a given observation function is adequate for state reconstruction.

**Connection to the main injectivity theorem.** The separating window theorem sits naturally alongside `delayEmbedding_injective_iff_separatesOrbits`, which establishes

\[
\Phi_k \text{ is injective} \;\iff\; \operatorname{SeparatesOrbits}(f, \alpha, k).
\]

Together, these two theorems give a complete picture: the injectivity--separation equivalence characterizes *what it means* for a given window to work, while the separating window theorem characterizes *whether any window can work at all* and how large it must be.

---

### Cross-links

- [Delay Embedding & Orbit Separation](delay-embedding.md) --- the `delayEmbedding` definition and `delayEmbedding_injective_iff_separatesOrbits`
- [Ordinal Compression](ordinal-compression.md) --- the `ordinalDelayMap` and pattern-count bounds built on the delay embedding
- [Theorem Catalog](../reference/theorems.md) --- full declaration inventory
