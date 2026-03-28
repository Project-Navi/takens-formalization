# TakensFormal

Lean 4 + Mathlib formalization of the Takens delay embedding theorem.

## Routes

**Route B (discrete):** Characterization of delay embedding injectivity
via orbit separation (`delayEmbedding_injective_iff_separatesOrbits`).
Ordinal compression theory via `ordinalDelayMap`. Zero sorry, zero axioms.

**Route A (smooth):** Classical smooth Takens embedding theorem on compact
manifolds. Skeleton — embedding chain and `SardInfra` axiom typeclass
planned. Genericity deferred — tracked in `debt.md`.

Route A and Route B are independent proof trees with no shared definitions.

## Build & verify

```bash
lake build --wfail                     # primary — warnings are errors
lake lint                              # Mathlib linter suite
lake build TakensFormal.Verify         # axiom dashboard (compilation check)
lake env lean TakensFormal/Verify.lean # display axiom output
```

## File structure

| File | Role | Route |
|------|------|-------|
| `OrdinalPattern.lean` | Bandt-Pompe ordinal pattern map | B |
| `DelayWindow.lean` | Delay embedding + SeparatesOrbits + characterization | B |
| `IteratePeriod.lean` | Period bridge lemmas | B |
| `TakensDiscrete.lean` | Future finite-horizon corollaries (skeleton) | B |
| `OrdinalTakens.lean` | Ordinal delay compression theory | B |
| `SardInfra.lean` | Sard axiom typeclass (skeleton) | A |
| `SmoothTakens.lean` | Smooth delay map (skeleton) | A |
| `Verify.lean` | Axiom dashboard (diagnostic) | Both |

## Axiom boundary

`TakensFormal.Verify` should report only `[propext, Classical.choice,
Quot.sound]` plus the axioms exposed via `SardInfra` (no hidden `sorryAx`).

Route B theorems carry no custom axioms. Route A theorems will depend on
`SardInfra`, which axiomizes `sard_of_finrank_gt` (not yet in Mathlib;
see `Mathlib.Geometry.Manifold.WhitneyEmbedding` TODO).

## AI disclosure

Parts of this formalization were developed with Claude (Anthropic) and
Aristotle (theorem prover). All code has been manually reviewed and
understood.
