# Coincidence Length and the Separating Horizon

For a *given* observation on a finite state space, which delay windows separate orbits, and
what is the shortest one? The coincidence length answers both questions exactly.

## Coincidence length

<div class="theorem-block" markdown>
<span class="badge badge--proved">Proved</span>
<span class="theorem-name">(coincidenceLength)</span>

The *coincidence length* \(c(x, y) \in \mathbb{N}_\infty\) is the first index \(i\) with
\(\alpha(f^i x) \ne \alpha(f^i y)\), or \(\infty\) if the observations always agree.
</div>

Two windows of length \(k\) agree exactly when \(k \le c(x, y)\)
(`delayEmbedding_eq_iff_le_coincidenceLength`). The coincidence length is symmetric, is
\(\infty\) on the diagonal, is \(0\) iff the first observations differ, and satisfies the
one-step recursion \(c(x, y) = c(fx, fy) + 1\) when \(\alpha(x) = \alpha(y)\)
(`coincidenceLength_of_eq`). Hence \(\alpha\) separates orbits at window \(k\) iff
\(c(x, y) < k\) for every pair of distinct states
(`separatesOrbits_iff_forall_coincidenceLength_lt`).

## The separating horizon

<div class="theorem-block" markdown>
<span class="badge badge--proved">Proved</span>
<span class="theorem-name">(separatesOrbits_iff_separatingHorizon_le)</span>

Let \(H = \sup_{x \ne y} (c(x, y) + 1) \in \mathbb{N}_\infty\) (`separatingHorizon`). Then a
window of length \(k\) separates orbits iff \(k \ge H\). When \(H\) is finite it is the
least separating window (`isLeast_separatingHorizon`).
</div>

\(H = 0\) iff there are no two distinct states, and a pair that is never distinguished
forces \(H = \infty\). On a finite state space the supremum is attained by a pair
(`exists_separatingHorizon_eq`), so \(H = \infty\) iff some distinct pair is never
distinguished (`separatingHorizon_eq_top_iff`). In particular some window separates orbits
iff every distinct pair is eventually distinguished (`exists_separatingWindow_iff`).

## A sharp bound

<div class="theorem-block" markdown>
<span class="badge badge--proved">Proved</span>
<span class="theorem-name">(separatingHorizon_le_card_sub_one)</span>

On \(N\) states a finite horizon is at most \(N - 1\). Equivalently, equal windows of length
\(N - 1\) force equal observations at every time (`forall_iterate_eq_of_delayEmbedding_eq`).
No injectivity of \(f\) or \(\alpha\) is assumed.
</div>

The proof tracks the partition of states by their windows of length \(j\). Each longer
window refines it, and once a refinement step changes nothing, no later step does. A
partition of \(N\) states can be strictly refined at most \(N - 1\) times, so the windows of
length \(N - 1\) already determine all observations.

The bound is attained. On the countdown chain \(i \mapsto i - 1\) on \(\{0, \dots, N-1\}\),
with \(0\) fixed and observed by the indicator of \(0\), the states \(N-1\) and \(N-2\)
first differ at time \(N - 2\), so exactly \(N - 1\) coordinates are needed
(`separatingHorizon_countdown`).

## Deciding separability

For states \(\mathrm{Fin}\,n\) and observations in a type with decidable equality,
`horizonSearch` scans the windows of length \(k < n\) and returns
either the first separating length or a distinct pair with equal windows of length
\(n - 1\), which by the sharp bound is never distinguished. Both answers are proved sound
and complete: the search returns `separating k` iff the horizon is \(k\)
(`horizonSearch_eq_separating_iff`), and a pair iff the horizon is infinite
(`exists_horizonSearch_eq_indistinguishable_iff`). Real-valued data needs a representation
with decidable equality, such as rationals; equality of reals is not decided.

## Scope

These are statements about exact observations of a finite model. A finite sample of a
continuous system is not a finite state space, and nothing here bounds the number of
measurements needed for noisy data.

### Cross-links

- [Delay Embedding & Orbit Separation](delay-embedding.md)
- [Ordinal Compression](ordinal-compression.md)
- [Theorem Catalog](../reference/theorems.md)
