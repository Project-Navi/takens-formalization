# Ordinal Compression

The ordinal pattern of a tie-free vector \(v : \{0, \dots, d-1\} \to \mathbb{R}\) is the
permutation \(\sigma\) that sorts it:

$$v(\sigma(0)) < v(\sigma(1)) < \cdots < v(\sigma(d-1)).$$

Ordinal patterns [BandtPompe2002] underlie permutation entropy and related complexity
measures. Applied to delay windows they give the *ordinal delay map*, a code that keeps the
order of the observations and discards their values. This page states what that code
preserves and what it cannot.

## Ordinal patterns

<div class="theorem-block" markdown>
<span class="badge badge--proved">Proved</span>
<span class="theorem-name">(ordinalPattern_exists_unique)</span>

A tie-free vector has exactly one ordinal pattern, and it is Mathlib's `Tuple.sort`
(`ordinalPattern_eq_tuple_sort`). Every permutation occurs (`ordinalPattern_surjective`),
so there are \(d!\) patterns of order \(d\) (`card_equiv_perm_fin`).
</div>

Two tie-free vectors have the same pattern iff every pair of coordinates is in the same
strict order (`ordinalPattern_eq_iff`).

**Transformations of the values.** A *strictly increasing* \(g\) preserves the pattern
(`ordinalPattern_comp_strictMono`). A *strictly decreasing* \(g\) reverses the order, and
the pattern becomes \(\sigma \circ \mathrm{rev}\), where \(\mathrm{rev}(i) = d - 1 - i\)
(`ordinalPattern_comp_strictAnti`). A transformation that is only monotone can create ties,
and then no pattern is defined.

## The ordinal delay map

On states whose delay window is tie-free (`WindowDistinct`), the ordinal delay map sends
\(x\) to the pattern of its window (`ordinalDelayMap`). It inherits the rules above: it is
unchanged by strictly increasing transformations of the observation
(`ordinalDelayMap_comp_strictMono`) and relabeled by \(\sigma \mapsto \sigma \circ
\mathrm{rev}\) under strictly decreasing ones (`ordinalDelayMap_comp_strictAnti`). Two
states have the same code iff their windows induce the same strict order
(`ordinalDelayMap_eq_iff`).

Along an orbit, `observedPatterns` collects the patterns of \(N\) consecutive windows (ties
included, via the stable sort). Their number is at most \(d!\), at most \(N\), and on a
periodic orbit at most the minimal period (`card_observedPatterns_le_factorial`,
`card_observedPatterns_le_length`, `card_observedPatterns_le_period`).

## Pattern entropy

`patternEntropy` is the Shannon entropy of the empirical distribution of patterns along
\(N\) windows. It is nonnegative and at most \(\log \min(d!, N)\), and at most the log of the
minimal period on a periodic orbit (`patternEntropy_le_log_min`,
`patternEntropy_le_log_min_period`). It is invariant under strictly increasing
transformations of the observation (`patternEntropy_comp_strictMono`) and, on tie-free
orbit segments, under strictly decreasing ones, which only relabel the patterns
(`patternEntropy_comp_strictAnti`).

## What an ordinal code retains

Exact state reconstruction and ordinal compression are different questions.

- **The code is not a reconstruction.** It takes at most \(k!\) values, so it is not
  injective on more than \(k!\) tie-free states, nor on infinitely many
  (`not_injective_ordinalDelayMap_of_factorial_lt`,
  `not_injective_ordinalDelayMap_of_infinite`). Exact reconstruction is a property of the
  delay map itself ([Delay Embedding](delay-embedding.md)).
- **Target sufficiency.** A quantity of the state can be computed from the code iff it is
  constant on the fibers of the code, and then the factor is unique
  (`exists_factor_iff`, `factor_unique`). The quotient of states by equality of codes is in
  bijection with the codes that occur (`ordinalQuotientEquivRange`).
- **Ordinal dynamics.** On a forward-invariant set of tie-free states, the codes evolve by
  a map on codes iff states with equal codes have next states with equal codes
  (`exists_ordinalDynamics_iff`).

These are exact statements about a model. They do not establish that a particular sensor,
data set or learning system satisfies their hypotheses.

## References

- [BandtPompe2002] C. Bandt and B. Pompe, *Permutation entropy: a natural complexity
  measure for time series*, Phys. Rev. Lett. 88 (2002), 174102.
- [BandtKellerPompe2002] C. Bandt, G. Keller and B. Pompe, *Entropy of interval maps via
  permutations*, Nonlinearity 15 (2002), 1595--1602.
