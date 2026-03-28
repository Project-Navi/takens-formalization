# Technical Debt Tracker

## Open

### Route A — Smooth Takens (proved under SardInfra axiom)
- [ ] **Sard's theorem** — Not in Mathlib. WhitneyEmbedding.lean has explicit TODO.
      Unblocks: tight Whitney 2m+1 bound AND Takens genericity argument.
- [ ] **Parametric transversality** — Blocked on Sard + parametric transversality theorem.
- [ ] **Sauer-Yorke-Casdagli (fractal extension)** — Requires prevalence theory +
      box-counting dimension, neither in Mathlib.

### Upstream candidates
- [ ] **ordinalPattern → Mathlib** — Bandt-Pompe ordinal pattern extractor.
      Natural Mathlib addition (Stats/TimeSeries or Combinatorics namespace).
      Post to Zulip before PR.
- [ ] **delayEmbedding → Mathlib** — Delay coordinate map for finite dynamical systems.
      Natural Mathlib addition (Dynamics or Combinatorics namespace).
- [ ] **SardInfra statement → Zulip** — Reference/design sketch for Sard formalization.
      Not a PR; value is as a precise Lean 4 statement shared on Zulip to inform
      upstream Sard work.

### Infrastructure
- [ ] **Axiom allowlist enforcement** — Upgrade `scripts/check-axioms.sh` from
      `sorryAx` check to full allowlist after SardInfra typeclass is designed (gate 3).
      Until then, axiom boundary is sorry-enforced but not allowlist-enforced.

## Resolved

### Infrastructure
- [x] **GitHub Actions CI** — `.github/workflows/lean_action_ci.yml` stood up.
      Sorry-free invariant now enforced on push/PR. SHA-pinned actions,
      Mathlib cache, concurrency group.
