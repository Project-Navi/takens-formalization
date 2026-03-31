# Theorem Catalog

All 42 verified declarations in the formalization, listed by source file.
Each declaration has been checked by `#print axioms` in
[`Verify.lean`](https://github.com/Project-Navi/takens-formalization/blob/main/TakensFormal/Verify.lean)
and depends only on Lean's foundational axioms (`propext`, `Classical.choice`, `Quot.sound`).
No `sorryAx` appears anywhere. See the [Axiom Dashboard](axiom-dashboard.md) for details.

---

## OrdinalPattern.lean (Route B)

| Declaration | Statement | Badge |
|---|---|---|
| `IsOrdinalPatternOf` | $\text{IsOrdinalPatternOf}(\sigma, f) \iff f \circ \sigma \text{ is strictly monotone}$ | <span class="badge badge--proved">Proved</span> |
| `ordinalPattern` | $\text{ordinalPattern}(f, h_f) \in S_d$ -- the unique permutation sorting an injective $f : \text{Fin}\,d \to \mathbb{R}$ | <span class="badge badge--proved">Proved</span> |
| `ordinalPattern_exists_unique` | For injective $f : \text{Fin}\,d \to \mathbb{R}$, $\exists!\, \sigma \in S_d$ such that $f \circ \sigma$ is strictly monotone | <span class="badge badge--proved">Proved</span> |
| `isOrdinalPatternOf_comp_strictMono` | If $\sigma$ is the ordinal pattern of $f$ and $g$ is strictly monotone, then $\sigma$ is the ordinal pattern of $g \circ f$ | <span class="badge badge--proved">Proved</span> |
| `ordinalPattern_surjective` | Every $\sigma \in S_d$ is the ordinal pattern of some injective $f : \text{Fin}\,d \to \mathbb{R}$ | <span class="badge badge--proved">Proved</span> |

## DelayWindow.lean (Route B)

| Declaration | Statement | Badge |
|---|---|---|
| `delayEmbedding` | $\Phi_{f,\alpha,k}(x) = \bigl(\alpha(x),\, \alpha(f(x)),\, \dots,\, \alpha(f^{k-1}(x))\bigr) \in \mathbb{R}^k$ | <span class="badge badge--proved">Proved</span> |
| `SeparatesOrbits` | $\text{SeparatesOrbits}(f, \alpha, k) \iff \forall\, x \neq y,\; \exists\, i < k,\; \alpha(f^i(x)) \neq \alpha(f^i(y))$ | <span class="badge badge--proved">Proved</span> |
| `delayEmbedding_injective_iff_separatesOrbits` | $\Phi_{f,\alpha,k} \text{ injective} \iff \text{SeparatesOrbits}(f, \alpha, k)$ | <span class="badge badge--proved">Proved</span> |
| `delayEmbedding_continuous` | If $f$ and $\alpha$ are continuous, then $\Phi_{f,\alpha,k}$ is continuous | <span class="badge badge--proved">Proved</span> |
| `coincidenceLength` | $c(x,y) = \min\{i \in \mathbb{N} : \alpha(f^i(x)) \neq \alpha(f^i(y))\} \in \mathbb{N}_\infty$ | <span class="badge badge--novel">Novel</span> |
| `exists_separatingWindow_iff` | On a finite type: $(\exists\, k,\; \text{SeparatesOrbits}(f,\alpha,k)) \iff \forall\, x \neq y,\; \exists\, i,\; \alpha(f^i(x)) \neq \alpha(f^i(y))$ | <span class="badge badge--novel">Novel</span> |
| `delayEmbedding_image_card_le` | $\lvert\operatorname{im} \Phi_{f,\alpha,k}\rvert \le \lvert X \rvert$ for finite $X$ | <span class="badge badge--proved">Proved</span> |
| `delayEmbedding_image_card_of_injective` | If $\Phi_{f,\alpha,k}$ is injective on finite $X$, then $\lvert\operatorname{im} \Phi_{f,\alpha,k}\rvert = \lvert X \rvert$ | <span class="badge badge--proved">Proved</span> |

## IteratePeriod.lean (Route B)

| Declaration | Statement | Badge |
|---|---|---|
| `separatesOrbits_of_injective` | If $\alpha$ is injective and $k \ge 1$, then $\text{SeparatesOrbits}(f, \alpha, k)$ | <span class="badge badge--proved">Proved</span> |
| `windowDistinct_of_injective_of_le_minimalPeriod` | If $\alpha$ is injective and $k \le \text{minPeriod}(f, x)$, then the delay window at $x$ has distinct values | <span class="badge badge--proved">Proved</span> |
| `isPeriodicPt_of_injective_iterate_eq` | If $f$ is injective and $f^i(x) = f^j(x)$ with $i \neq j$, then $x$ is periodic | <span class="badge badge--proved">Proved</span> |
| `windowDistinct_of_injective_orbit` | If $\alpha$ is injective and the orbit of $x$ is non-repeating within $k$ steps, the delay window values are distinct | <span class="badge badge--proved">Proved</span> |

## OrdinalTakens.lean (Route B)

| Declaration | Statement | Badge |
|---|---|---|
| `ordinalDelayMap` | $\pi_{f,\alpha,k}(x) = \text{ordinalPattern}(\Phi_{f,\alpha,k}(x))$ for states with tie-free windows | <span class="badge badge--proved">Proved</span> |
| `ordinalDelayMap_monotone_invariant` | If $g : \mathbb{R} \to \mathbb{R}$ is strictly monotone, then $\pi_{f,\, g \circ \alpha,\, k} = \pi_{f,\alpha,k}$ | <span class="badge badge--proved">Proved</span> |
| `ordinalDelayMap_eq_of_order_eq` | If two states share the same relative ordering in their delay windows, they have the same ordinal pattern | <span class="badge badge--proved">Proved</span> |
| `observedPatterns` | $\text{observedPatterns}(f,\alpha,d,x,N) \subseteq S_d$ -- the set of ordinal patterns seen along an orbit of length $N$ | <span class="badge badge--proved">Proved</span> |
| `card_observedPatterns_le_factorial` | $\lvert\text{observedPatterns}(f,\alpha,d,x,N)\rvert \le d!$ | <span class="badge badge--proved">Proved</span> |
| `card_observedPatterns_le_length` | $\lvert\text{observedPatterns}(f,\alpha,d,x,N)\rvert \le N$ | <span class="badge badge--proved">Proved</span> |
| `card_observedPatterns_le_period` | For periodic $x$: $\lvert\text{observedPatterns}(f,\alpha,d,x,N)\rvert \le \text{minPeriod}(f, x)$ | <span class="badge badge--proved">Proved</span> |

## SardInfra.lean (Route A)

| Declaration | Statement | Badge |
|---|---|---|
| `criticalSet` | $\text{Crit}(f) = \{x : \text{fderiv}_{\mathbb{R}}\, f(x) \text{ is not surjective}\}$ | <span class="badge badge--proved">Proved</span> |
| `criticalValues` | $\text{CritVal}(f) = f(\text{Crit}(f))$ | <span class="badge badge--proved">Proved</span> |
| `det_fderiv_eq_zero_of_not_surjective` | If $L : E \to_L E$ is not surjective, then $\det L = 0$ | <span class="badge badge--proved">Proved</span> |
| `ContinuousLinearMap.surjective_iff_det_ne_zero` | $L : E \to_L E$ is surjective $\iff \det L \neq 0$ | <span class="badge badge--proved">Proved</span> |
| `criticalSet_eq_det_zero` | $\text{Crit}(f) = \{x : \det(\text{fderiv}_{\mathbb{R}}\, f(x)) = 0\}$ for endomorphisms | <span class="badge badge--proved">Proved</span> |
| `isClosed_criticalSet_of_contDiff` | If $f : E \to E$ is $C^\infty$, then $\text{Crit}(f)$ is closed | <span class="badge badge--proved">Proved</span> |
| `sard_equidim` | If $f : E \to E$ is $C^\infty$, then $\mu(\text{CritVal}(f)) = 0$ for any additive Haar measure $\mu$ | <span class="badge badge--proved">Proved</span> |
| `sard_low_dim` | If $f : E \to F$ is $C^\infty$ and $\dim E < \dim F$, then $\mu(\text{CritVal}(f)) = 0$ | <span class="badge badge--proved">Proved</span> |
| `exists_continuousLinearEquiv_of_finrank_eq` | If $\dim_{\mathbb{R}} E = \dim_{\mathbb{R}} F$, there exists a continuous linear equivalence $E \simeq_L F$ | <span class="badge badge--proved">Proved</span> |
| `criticalSet_comp_equiv` | $\text{Crit}(e \circ f) = \text{Crit}(f)$ for a continuous linear equivalence $e$ | <span class="badge badge--proved">Proved</span> |
| `ContinuousLinearEquiv.symm_preimage_eq_image` | $e^{-1}{}^{\leftarrow}(S) = e(S)$ for a continuous linear equivalence | <span class="badge badge--proved">Proved</span> |
| `map_continuousLinearEquiv_isAddHaarMeasure` | $\text{map}\, e^{-1}\, \mu$ is an additive Haar measure when $\mu$ is | <span class="badge badge--proved">Proved</span> |
| `sard_equidim_general` | If $f : E \to F$ is $C^\infty$ and $\dim E = \dim F$, then $\mu(\text{CritVal}(f)) = 0$ | <span class="badge badge--proved">Proved</span> |

## SmoothTakens.lean (Route A)

| Declaration | Statement | Badge |
|---|---|---|
| `smoothDelayMap` | $\Psi_{T,h,n}(x) = \bigl(h(x),\, h(T(x)),\, \dots,\, h(T^{n-1}(x))\bigr) \in \mathbb{R}^n$ | <span class="badge badge--axiom-free">Axiom-free</span> |
| `smoothDelayMap_continuous` | If $T$ and $h$ are continuous, then $\Psi_{T,h,n}$ is continuous | <span class="badge badge--axiom-free">Axiom-free</span> |
| `smoothDelayMap_isClosedEmbedding` | If $X$ is compact and $\Psi_{T,h,n}$ is injective, then $\Psi_{T,h,n}$ is a closed embedding | <span class="badge badge--axiom-free">Axiom-free</span> |
| `smoothDelayMap_isEmbedding` | If $X$ is compact and $\Psi_{T,h,n}$ is injective, then $\Psi_{T,h,n}$ is an embedding | <span class="badge badge--axiom-free">Axiom-free</span> |
| `smoothDelayMap_rangeHomeomorph` | If $X$ is compact and $\Psi_{T,h,n}$ is injective, then $X \cong \operatorname{im}\Psi_{T,h,n}$ | <span class="badge badge--axiom-free">Axiom-free</span> |

---

**Total: 42 declarations.** 0 `sorry`. 0 custom axioms.
