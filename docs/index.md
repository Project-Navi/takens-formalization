---
hide:
  - navigation
  - toc
---

# Takens Formalization

**Lean 4 + Mathlib formalization of delay embedding theory --- with a novel coincidence length result.**

42 declarations across two independent proof routes. Zero sorry, zero custom axioms.

[Read the Exposition](exposition/proof-architecture.md){ .md-button .md-button--primary }
[Theorem Catalog](reference/theorems.md){ .md-button }

---

## What is proved

This formalization covers both the discrete combinatorial and smooth topological
aspects of delay embedding, organized into two independent proof routes that share
no definitions.

### Novel contribution

| Result | Statement | File |
|--------|-----------|------|
| Coincidence length | For finite dynamical systems, a (possibly non-injective) observation separates orbits at window \(k\) iff every coincidence between distinct orbits has length \(< k\). | `DelayWindow.lean` |

This extends Takens' 1981 theorem, which establishes generic injectivity but says
nothing about *when* non-injective observations still suffice.

### Route B --- Discrete (24 declarations)

| Result | Statement | File |
|--------|-----------|------|
| Injectivity iff orbit separation | \(\Phi_{f,\alpha,k}\) is injective \(\iff\) \(\alpha\) separates orbits at window \(k\) | `DelayWindow.lean` |
| Ordinal pattern well-definedness | Unique permutation \(\sigma\) such that \(\alpha \circ \sigma\) is strictly monotone | `OrdinalPattern.lean` |
| Monotone invariance | Ordinal delay map is invariant under monotone transformation of the observation | `OrdinalTakens.lean` |
| Pattern count bounds | \(\lvert\mathrm{observedPatterns}\rvert \leq k!\), \(\leq \mathrm{length}\), \(\leq \mathrm{period}\) | `OrdinalTakens.lean` |

### Route A --- Smooth (18 declarations)

| Result | Statement | File |
|--------|-----------|------|
| Closed embedding | Compact + injective \(\Rightarrow\) closed embedding | `SmoothTakens.lean` |
| Homeomorphism onto image | The delay map restricts to a homeomorphism onto its range | `SmoothTakens.lean` |
| Sard equidimensional | Critical values have measure zero (equal-dimension case) | `SardInfra.lean` |
| Sard low-dimensional | Critical values have measure zero (low-dimension case, via Hausdorff dimension) | `SardInfra.lean` |

Route A's embedding chain (`SmoothTakens.lean`) is fully axiom-free --- it does
not import `SardInfra`.

**Axiom boundary:** All results depend only on `propext`, `Classical.choice`, and
`Quot.sound` --- Lean's standard logical axioms. Zero custom axioms.

---

## Documentation

| Section | What you'll find |
|---------|-----------------|
| [Quickstart](getting-started/quickstart.md) | Build and verify the proofs |
| [Proof Architecture](exposition/proof-architecture.md) | Why two routes, what formal proof reveals |
| [Coincidence Length](exposition/coincidence-length.md) | The novel contribution --- what Takens didn't prove |
| [Theorem Catalog](reference/theorems.md) | All 42 declarations with LaTeX statements |
| [Axiom Dashboard](reference/axiom-dashboard.md) | What the axiom boundary means |
| [Open Problems](research/open-problems.md) | What remains, tiered by difficulty |
| [navi-SAD Bridge](bridge/navi-sad.md) | How these proofs back the empirical instrument |
