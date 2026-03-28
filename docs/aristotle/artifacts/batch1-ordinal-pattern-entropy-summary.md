# Summary of changes
Successfully formalized and proved the complete theory of ordinal pattern entropy bounds for finite dynamical systems in `RequestProject/OrdinalPatternEntropy.lean`.

## Definitions

- **`lexLt`**: Strict lexicographic order on (value, index) pairs for tie-breaking in rankings
- **`rankFn` / `rankFinFn`**: The rank of an element in a sequence — the number of elements strictly smaller in the lexicographic order
- **`ordinalPattern`**: The ordinal pattern of a finite real-valued sequence `v : Fin d → ℝ`, defined as the ranking permutation in `Equiv.Perm (Fin d)` (constructed via `Equiv.ofBijective` after proving the rank function is injective)
- **`delayWindow`**: The delay-coordinate observation window `(α(f^n x), α(f^{n+1} x), …, α(f^{n+d-1} x))`
- **`orbPattern`**: The ordinal pattern at step `n` of the orbit
- **`patternSet`**: The finset of distinct ordinal patterns along an orbit of length `N`
- **`statePattern`**: The state-pattern map showing the pattern is determined by the current state

## Theorems Proved

1. **`card_patternSet_le_N`**: The number of distinct ordinal patterns is at most `N` (trivially, as image of `range N`)
2. **`card_patternSet_le_factorial`**: The number of distinct ordinal patterns is at most `d!` (since patterns are permutations of `Fin d`, and `|Equiv.Perm (Fin d)| = d!`)
3. **`card_patternSet_le_card`**: The number of distinct ordinal patterns is at most `card X` (since the pattern factors through the state space via `orbPattern_eq_statePattern`)
4. **`card_patternSet_le_min`**: Combined bound: at most `min(N, min(d!, card X))`
5. **`orbPattern_periodic`**: On a periodic orbit of period `p`, the ordinal pattern function has period `p`
6. **`card_patternSet_le_period`**: On a periodic orbit of period `p`, the number of distinct patterns is at most `p`

All proofs compile without `sorry` and use only standard axioms (`propext`, `Classical.choice`, `Quot.sound`).