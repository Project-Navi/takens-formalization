# Technical Debt Tracker

## Open

### Route A — Smooth Takens (genericity blocked on SardInfra)
- [ ] **Sard equidimensional case** — NEXT HEADLINE TARGET. Provable from
      Mathlib area formula (`addHaar_image_le_lintegral_abs_det_fderiv`).
      Aristotle artifact exists at `docs/aristotle/artifacts/batch1-sard-low-dim.lean.txt`
      but needs import work. `det_fderiv_eq_zero_of_not_surjective` already proved.
- [ ] **Sard low-dim integration** — Aristotle proved `addHaar_image_eq_zero_of_finrank_lt`
      via Hausdorff dimension. Needs granular import work to compile on 4.28.0.
- [ ] **SardInfra typeclass body** — Gate 3. Axiomize only `sard_of_finrank_gt`.
      Equidimensional and low-dim cases will be proved, not axiomized.
- [ ] **Parametric transversality** — Blocked on Sard + transversality theorem.
- [ ] **Sauer-Yorke-Casdagli (fractal extension)** — Requires prevalence theory +
      box-counting dimension, neither in Mathlib.

### Route B — Future depth
- [ ] **SmoothTakens additional lemmas** — `smoothDelayMap_shift`,
      `smoothDelayMap_injective_iff`, `smoothDelayMap_injective_of_le` planned
      in gate 3 spec but not yet implemented.

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

### Route B
- [x] **OrdinalPattern** — property-first design, 8 theorems proved
- [x] **DelayWindow headline** — `delayEmbedding_injective_iff_separatesOrbits` +
      `coincidenceLength` + `exists_separatingWindow_iff`
- [x] **IteratePeriod bridge** — 4 theorems connecting to Mathlib PeriodicPts API
- [x] **OrdinalTakens compression** — `ordinalDelayMap` + observedPatterns bounds

### Route A
- [x] **SmoothTakens embedding chain** — continuity → closed embedding →
      homeomorphism, axiom-free
- [x] **SardInfra det helper** — `det_fderiv_eq_zero_of_not_surjective`
