# Summary of changes
Successfully formalized and proved a complete theory of delay embeddings for finite dynamical systems in Lean 4 with Mathlib. The file is at `RequestProject/DelayEmbedding.lean`.

## Definitions
- **`delayEmbedding f α k x`**: Maps a point `x` to the observation tuple `(α(x), α(f(x)), ..., α(f^k(x)))` as a function `Fin (k+1) → ℝ`.
- **`SeparatesOrbits f α k`**: The delay embedding with observation `α` and window length `k` is injective.
- **`coincidenceLength f α x y`**: The first iterate `i` where `α(f^i(x)) ≠ α(f^i(y))`, or `⊤` if orbits always agree under `α`. Uses `ℕ∞` to cleanly handle the infinite case.

## Proved Theorems (all sorry-free, verified with `lake build`)

1. **`separatesOrbits_iff`** — *Characterization*: The delay embedding is injective iff for all distinct `x, y`, there exists `i ≤ k` with `α(f^i(x)) ≠ α(f^i(y))`.

2. **`separatesOrbits_mono`** — *Monotonicity*: Separation at window `k` implies separation at any larger window `k' ≥ k`.

3. **`separatesOrbits_of_injective`** — *Injective observation*: If `α` is injective, it separates orbits at any window length (even `k = 0`), regardless of `f`.

4. **`exists_separating_window_iff`** — *Non-injective characterization*: A (possibly non-injective) `α` admits an injective delay embedding for some window length iff for every distinct pair, their orbits eventually produce different `α`-values. The backward direction uses finiteness of `X` to take the maximum first-disagreement over all pairs.

5. **`coincidenceLength_eq_zero`** — The coincidence length is zero when `α` directly distinguishes the two points.

6. **`separatesOrbits_iff_coincidence`** — *Coincidence length relationship*: Separation at window `k` ↔ all coincidence lengths are at most `k`. This precisely relates the minimum separating window to the maximum coincidence length over all distinct orbit pairs.

7. **`separatesOrbits_card_of_bijective`** — *Permutation theorem*: For bijective `f` and injective `α`, `k = card X` suffices. (This is a corollary of `separatesOrbits_of_injective`, since injective `α` already separates at any window.)

All proofs use only standard axioms (`propext`, `Classical.choice`, `Quot.sound`).