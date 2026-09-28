# Delay Embedding & Orbit Separation

Given dynamics \(f : X \to X\) and an observation \(\alpha : X \to Y\) (any type of values),
the delay map of window length \(k\) records \(k\) consecutive observations along the orbit:

$$\Phi_k(x) \;=\; \bigl(\alpha(x),\; \alpha(fx),\; \dots,\; \alpha(f^{k-1}x)\bigr) \in Y^k.$$

In Lean this is `delayEmbedding f α k`, defined once in `DelayWindow` and used unchanged by
every other module, including the smooth ones.

## Injectivity is orbit separation

<div class="theorem-block" markdown>
<span class="badge badge--proved">Proved</span>
<span class="theorem-name">(delayEmbedding_injective_iff_separatesOrbits)</span>

\(\Phi_k\) is injective iff \(\alpha\) *separates orbits at window \(k\)*: whenever
\(\alpha(f^i x) = \alpha(f^i y)\) for all \(i < k\), then \(x = y\).
</div>

```lean
theorem delayEmbedding_injective_iff_separatesOrbits
    (f : X → X) (α : X → Y) (k : ℕ) :
    Injective (delayEmbedding f α k) ↔ SeparatesOrbits f α k
```

The statement is an unfolding of definitions, and it is the reason the rest of the finite
theory is about orbit separation rather than injectivity. Separation is monotone in the
window (`separatesOrbits_of_le`), and a window of length \(k+1\) is the first observation
followed by the window of length \(k\) at the next state (`delayEmbedding_succ_eq_iff`),
which is the recursion behind the [coincidence length](coincidence-length.md). A sampling
lag \(q\) is the delay map of \(f^q\) (`delayEmbedding_iterate_apply`).

The delay map is continuous for continuous data (`delayEmbedding_continuous`). On a finite
type it takes at most \(|X|\) values, exactly \(|X|\) when injective
(`delayEmbedding_image_card_le`, `delayEmbedding_image_card_of_injective`).

## Tie-free windows and periods

Ordinal codes need windows without ties (`WindowDistinct`). For an injective observation, a
window is tie-free as long as the orbit segment does not repeat
(`windowDistinct_of_injective_orbit`), in particular when \(k\) is at most the minimal
period (`windowDistinct_of_injective_of_le_minimalPeriod`). For injective \(f\), a repeated
iterate forces a periodic point (`isPeriodicPt_of_injective_iterate_eq`), and an injective
observation separates orbits at every \(k \ge 1\) (`separatesOrbits_of_injective`).

## Reconstruction on the image

If \(\Phi_k\) is injective, the dynamics can be read off the image. The decoder
\(\Phi_k^{-1}\) (`delayDecoder`) and the transported map
\(\Phi_k \circ f \circ \Phi_k^{-1}\) (`reconstructedDynamics`) satisfy the conjugacy
\(\Phi_k(x) \mapsto \Phi_k(fx)\), and in coordinates the new window is the old one shifted,
with only the last entry new (`reconstructedDynamics_apply_of_lt`). For compact \(X\),
continuous data and Hausdorff \(Y\), \(\Phi_k\) is a homeomorphism onto its image and the
reconstructed dynamics is continuous and topologically conjugate to \(f\)
(`delayHomeomorph`, `reconstructedDynamics_eq_conj`).

This is exact state reconstruction from exact observations of a mathematical model. It
does not say anything about noisy or finitely sampled data.

## Where the smooth theory starts

Takens' theorem [Takens1981] is about when \(\Phi_{2d+1}\) is injective, and an immersion,
for smooth data on a \(d\)-manifold. The same `delayEmbedding` is used there; see
[Smooth Embedding](smooth-embedding.md). The finite theory answers a different question:
for a given observation on a finite state space, which windows work
([Coincidence Length](coincidence-length.md)).

!!! tip "Measured data"
    See [Measured Data](measured-data.md) for what these results do and do not establish
    about measured time series.
