# Axiom Audit Report - TakensFormal @ v4.34.1

Date: 2026-11-01 (CST). Environment: navi-quick container, /task34.

- Lean toolchain: v4.34.1
- Mathlib: d13f23b723 (bump toolchain to v4.34.1)
- Full build: 8982 jobs, 0 errors (navi-quick container, since decommissioned; reproduce at this commit with `lake exe cache get && lake build`, lean-toolchain v4.34.1)

## Headline theorems - #print axioms verdicts

Raw output of lake env lean on the three headline theorems:

```
'dimH_image_le_sardMoreiraBound_of_finrank_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'dense_setOf_isContMDiffEmbedding_delayEmbedding_pair' depends on axioms: [propext, Classical.choice, Quot.sound]
'smoothDelayMap_isEmbedding' depends on axioms: [propext, Classical.choice, Quot.sound]
```

| Theorem | File | Statement |
|---|---|---|
| dimH_image_le_sardMoreiraBound_of_finrank_le | TakensFormal/ForMathlib/SardMoreira/MainTheorem.lean | Hausdorff-dimension form of the Sard-Moreira theorem |
| dense_setOf_isContMDiffEmbedding_delayEmbedding_pair | TakensFormal/GenericPairTakens.lean | Takens (1981): delay embeddings are dense (generic) in the C² pair topology |
| smoothDelayMap_isEmbedding | TakensFormal/SmoothTakens.lean | the smooth delay map is an embedding |

All three depend only on the three standard Lean axioms (propext, Classical.choice, Quot.sound) - **no sorryAx, no additional postulates**. Every result is machine-checked and complete.

## Method

#print axioms <name> reports the transitive axiom closure. A verdict is clean iff the list is a subset of {propext, Classical.choice, Quot.sound}. Note for reproduction: constants in files without a top-level namespace must be referenced by bare name (no module-path prefix).
