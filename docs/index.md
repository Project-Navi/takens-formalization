---
hide:
  - navigation
  - toc
---

# Takens Formalization

**A Lean 4 and Mathlib formalization of delay-coordinate reconstruction, from finite state
spaces to compact manifolds.**

Every selected declaration depends only on Lean's standard logical axioms. There are no
`sorry`s, no custom axioms and no assumption classes.

[Read the Exposition](exposition/proof-architecture.md){ .md-button .md-button--primary }
[Theorem Catalog](reference/theorems.md){ .md-button }

---

## What is proved

The delay map of dynamics \(T : X \to X\) and an observation \(h : X \to \mathbb{R}\) is
\(x \mapsto (h(x), h(Tx), \dots, h(T^{k-1}x))\), `delayEmbedding` in Lean.

| Area | Result | Module |
|------|--------|--------|
| Manifolds | On a compact smooth \(d\)-manifold there are finitely many smooth functions \(\varphi_q\) such that for every injective \(C^2\) map \(T\) with injective differentials and no periodic points of period \(\le 4d\), and every \(C^2\) observation \(h\), the delay map of \(h + \sum_q a_q \varphi_q\) with \(2d+1\) coordinates is a \(C^2\) embedding for Lebesgue-almost every \(a\) | `InterpolatingFamily` |
| Manifolds | Differential of the delay map, immersion criterion, compact injective immersions are embeddings; the identity never immerses in dimension \(\ge 2\) | `SmoothDelay` |
| Measure | Sard's theorem for \(C^r\) maps between finite-dimensional spaces, \(r \ge \dim E - \dim F + 1\), with local and open-set versions | `Sard` |
| Measure | Almost every member of a finite-dimensional affine family avoids a lower-dimensional set, is an immersion, or separates points | `GenericFamily` |
| Finite | Injectivity iff orbit separation; the exact separating horizon; the sharp bound \(N-1\) on \(N\) states, attained; a sound and complete decision procedure | `DelayWindow`, `TakensDiscrete` |
| Finite | Reconstruction of the dynamics on the delay image, a homeomorphism for compact spaces | `Reconstruction` |
| Ordinal | Ordinal patterns, invariance under strictly increasing and relabeling under strictly decreasing transformations, pattern counts and entropy bounds, what the code retains | `OrdinalTakens`, `OrdinalEntropy`, `OrdinalQuotient` |

**Not yet formalized here:** Takens' theorem for generic pairs \((T, h)\) in the \(C^2\)
topology. Periodic points of period at most \(2d\), the genericity of \(T\), and the
Baire-category assembly remain; see [Open Problems](research/open-problems.md).

---

## Documentation

| Section | What you'll find |
|---------|-----------------|
| [Quickstart](getting-started/quickstart.md) | Build and verify the proofs |
| [Proof Architecture](exposition/proof-architecture.md) | How the modules fit together |
| [Delay Embedding](exposition/delay-embedding.md) | Injectivity and orbit separation |
| [Coincidence Length](exposition/coincidence-length.md) | Exact horizons on finite state spaces |
| [Ordinal Compression](exposition/ordinal-compression.md) | What an ordinal code keeps |
| [Smooth Embedding](exposition/smooth-embedding.md) | Differentials, immersions and generic observations |
| [Sard's Theorem](exposition/sard-infrastructure.md) | Critical values at finite regularity |
| [Theorem Catalog](reference/theorems.md) | The selected declarations, by module |
| [Axiom Dashboard](reference/axiom-dashboard.md) | What the axiom records certify |
| [Roadmap](research/roadmap.md) | What comes next |
| [navi-SAD Bridge](bridge/navi-sad.md) | What these proofs do and do not say about the instrument |
