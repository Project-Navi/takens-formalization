# Aristotle Independent Verification — TakensFormal

**These artifacts are not reproducible on the current toolchain.**
They are retained as a historical record of the verification experiment,
not as drop-in replacements for the proofs in `TakensFormal/`.

The `artifacts/` directory contains sorry-stubbed versions of the project's
Lean files, submitted to [Aristotle](https://aristotle.harmonic.fun) for
independent proof synthesis.

## Results

### Batch 0 — Exploratory API Reconnaissance

12/12 lemmas proved. See `artifacts/batch0-exploration.lean.txt`.
Additional runs: topological Takens (12/12), Sard decomposition (2/3),
Bandt-Pompe ordinal patterns (8/8). See `artifacts/batch0-*.lean.txt`.

### Planned batches

| Batch | Target file | Scope | Status |
|-------|-------------|-------|--------|
| 1 | OrdinalPattern | Positivity, decidability, characterization lemmas | Planned |
| 2 | DelayWindow | Shift lemmas, cast-control, Fin arithmetic | Planned |
| 3 | IteratePeriod | Period bounds, orbit cardinality, pigeonhole | Planned |
| 4 | TakensDiscrete | Injectivity core, index arithmetic | Planned |

## File naming conventions

- `batch{N}-{target}.lean` — sorry-stubbed inputs as submitted
- `batch{N}-{target}.lean.txt` — Aristotle output (artifacts)

These files are outside the `TakensFormal/` build tree and are **not compiled
by `lake build`**. Do not rely on them for correctness claims.
