# Glossary

Definitions of key terms used throughout this formalization.

---

**axiom boundary**
: The interface between fully proved results and those that rely on external axioms or typeclasses. In this project, the `SardInfra` module contains all axiom-sensitive infrastructure; `SmoothTakens` is entirely axiom-free. See [Sard Infrastructure](../exposition/sard-infrastructure.md).

**closed embedding**
: A continuous injective map whose image is closed in the codomain. In the embedding chain, compact + injective implies closed embedding. See [Smooth Embedding Chain](../exposition/smooth-embedding.md).

**coincidence length**
: The index of the first iterate where two states produce different observations: $c(x,y) = \min\{i : \alpha(f^i(x)) \neq \alpha(f^i(y))\}$, or $\infty$ if their observed orbits always agree. See [Coincidence Length](../exposition/coincidence-length.md).

**compact space**
: A topological space where every open cover has a finite subcover. Compactness is the key hypothesis that upgrades a continuous injection to a closed embedding in Route A. See [Smooth Embedding Chain](../exposition/smooth-embedding.md).

**critical set**
: The set of points where the derivative of a smooth map is not surjective: $\text{Crit}(f) = \{x : \text{fderiv}\, f(x) \text{ is not surjective}\}$. See [Sard Infrastructure](../exposition/sard-infrastructure.md).

**critical values**
: The image of the critical set under the map: $\text{CritVal}(f) = f(\text{Crit}(f))$. Sard's theorem says this set has measure zero. See [Sard Infrastructure](../exposition/sard-infrastructure.md).

**delay embedding**
: The map $\Phi_{f,\alpha,k}(x) = (\alpha(x), \alpha(f(x)), \ldots, \alpha(f^{k-1}(x)))$ that reconstructs state-space structure from a scalar time series. See [Delay Embedding](../exposition/delay-embedding.md).

**Fintype**
: A Lean typeclass asserting that a type has finitely many elements. Used in Route B to take finite maxima and count distinct delay windows. See [Delay Embedding](../exposition/delay-embedding.md).

**homeomorphism**
: A continuous bijection whose inverse is also continuous. The strongest conclusion of the embedding chain: when the delay map is injective on a compact space, the domain is homeomorphic to the image. See [Smooth Embedding Chain](../exposition/smooth-embedding.md).

**injective**
: A function $f$ is injective if $f(x) = f(y)$ implies $x = y$. Injectivity of the delay embedding is the central property characterized in Route B. See [Delay Embedding](../exposition/delay-embedding.md).

**minimal period**
: The smallest positive integer $p$ such that $f^p(x) = x$. On a finite type, every point has finite minimal period. Window distinctness requires $k \le \text{minPeriod}(f, x)$. See [Delay Embedding](../exposition/delay-embedding.md).

**monotone invariance**
: The property that ordinal patterns are preserved under strictly monotone transformations of the observation function. Formally: if $g$ is strictly monotone, then $\pi_{f,\, g \circ \alpha,\, k} = \pi_{f,\alpha,k}$. See [Ordinal Compression](../exposition/ordinal-compression.md).

**observation function**
: A scalar-valued function $\alpha : X \to \mathbb{R}$ applied to each state in a dynamical system. The delay embedding constructs vectors from iterated observations. See [Delay Embedding](../exposition/delay-embedding.md).

**ordinal pattern**
: The unique permutation $\sigma \in S_d$ such that $f \circ \sigma$ is strictly monotone, where $f : \text{Fin}\, d \to \mathbb{R}$ is injective. Captures relative ordering, discarding magnitude. See [Ordinal Compression](../exposition/ordinal-compression.md).

**orbit separation**
: The property that an observation function distinguishes all pairs of states within $k$ iterates. Equivalent to injectivity of the delay embedding. See [Delay Embedding](../exposition/delay-embedding.md).

**permutation entropy**
: A complexity measure for time series based on the distribution of ordinal patterns along an orbit. The cardinality bounds on `observedPatterns` are the formal foundation. See [Ordinal Compression](../exposition/ordinal-compression.md).

**Route A**
: The smooth/topological proof path. Establishes that a continuous injective delay map on a compact space is a closed embedding and a homeomorphism onto its image. See [Proof Architecture](../exposition/proof-architecture.md).

**Route B**
: The discrete/combinatorial proof path. Characterizes delay embedding injectivity via orbit separation, defines coincidence length and ordinal compression, and proves pattern-count bounds. See [Proof Architecture](../exposition/proof-architecture.md).

**Sard's theorem**
: The set of critical values of a smooth map has measure zero. Proved here for the equidimensional case (via the Jacobian area formula) and the low-dimensional case (via Hausdorff dimension). See [Sard Infrastructure](../exposition/sard-infrastructure.md).

**SeparatesOrbits**
: The Lean predicate stating that $\alpha$ distinguishes all pairs of states within $k$ iterates: $\forall\, x\, y,\; (\forall\, i < k,\; \alpha(f^i(x)) = \alpha(f^i(y))) \to x = y$. See [Delay Embedding](../exposition/delay-embedding.md).

**sorry**
: A Lean tactic that closes any goal without proof, leaving a `sorryAx` marker in the axiom trace. Its presence indicates an incomplete proof. This formalization has zero `sorry` on the main branch. See [Axiom Dashboard](axiom-dashboard.md).

**surjective**
: A function $f : E \to F$ is surjective if every element of $F$ is in the image of $f$. A linear map is surjective iff its determinant is nonzero (in finite dimensions, for endomorphisms). See [Sard Infrastructure](../exposition/sard-infrastructure.md).

**WindowDistinct**
: The Lean predicate asserting that a state's delay window has no ties: the values $\alpha(f^i(x))$ are distinct for distinct $i < k$. Required for ordinal pattern extraction. See [Ordinal Compression](../exposition/ordinal-compression.md).
