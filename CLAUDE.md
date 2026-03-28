# CLAUDE.md — TakensFormal

## Project

Lean 4 (v4.28.0) + Mathlib (v4.28.0) formalization of the Takens delay embedding theorem.

- **Route B (discrete):** `delayEmbedding_injective_iff_separatesOrbits` — characterization
  of when delay embedding is injective via orbit separation. Ordinal compression theory
  via `ordinalDelayMap`. Zero sorry, zero axioms.
- **Route A (smooth):** `smoothTakens` — classical smooth Takens on compact manifolds,
  proved under `SardInfra` axiom typeclass.

Route A and Route B are independent proof trees with no shared definitions.
`delayEmbedding` (Route B, `DelayWindow.lean`) and `smoothDelayMap` (Route A,
`SmoothTakens.lean`) have incompatible types.

No cross-route imports: Route A never imports Route B files, Route B never imports
`SardInfra`. `Verify.lean` is the only file that sees both routes.

Zero sorry on main. Progressive enforcement:
- **Social** (scaffold → gate 1.5): developer discipline only.
- **Sorry-enforced** (gate 1.5): CI runs `lake build --wfail` + `scripts/check-axioms.sh`.
- **Axiom-allowlist** (gate 3, after SardInfra designed): fails on unexpected axioms.

Mathlib HEAD audit gate: no local mathlib fork, `rev = v4.28.0` treated as audit gate —
no `require` overrides. A version bump is warranted only if PeriodicPts/Finset.sort API
changed or Sard infrastructure landed.

## Build & verify

```bash
lake build --wfail                     # primary check — warnings are errors
lake lint                              # Mathlib linter suite
lake build TakensFormal.Verify         # axiom dashboard (explicit target, NOT in root import)
lake env lean TakensFormal/Verify.lean # display axiom output
```

`lintDriver = "batteries/runLinter"` borrowed from fd/cd-formalization for consistency.
Pre-commit hooks enforce: trailing whitespace, EOF newline, merge conflicts,
copyright headers on all `.lean` files, gitleaks.

## Lean style (Mathlib conventions)

### Naming

- **Prop terms** (theorems): `snake_case` — `mul_comm`, `delayEmbedding_injective`
- **Types/Props/Sorts** (structures): `UpperCamelCase` — `SardInfra`, `OrdinalPattern`
- **Other Type terms**: `lowerCamelCase` — `delayEmbedding`, `smoothDelayMap`
- **UpperCamelCase inside snake_case**: becomes `lowerCamelCase` — `neZero_iff` not `NeZero_iff`
- **Conclusion-first**: `lt_of_le_of_ne` (conclusion `lt`, hypotheses `le` and `ne`)
- **`_of_` pattern**: hypotheses joined by `_of_` in order: `C_of_A_of_B` for `A → B → C`
- **American English**: `factorization` not `factorisation`

### Formatting

- **100-char line limit** (linter-enforced)
- **`by` at end of preceding line**, never on its own line
- **2-space indent** for proof bodies; **4-space** for multi-line statements
- **No empty lines** inside declarations (linter-enforced)
- **Focusing dots** `·` flush with current indent, tactics indented beneath
- **`:`, `:=`, infix ops** at end of line, not start of next
- **`fun x ↦`** not `λ x ↦`; **no `$`** (use `<|` if needed)

### Tactics

| Goal type | Preferred tactic |
|-----------|-----------------|
| Linear ℕ/ℤ arithmetic | `omega` |
| Numerical evaluation | `norm_num` |
| Decidable props | `decide` |
| Positivity (0 ≤ x, 0 < x) | `positivity` |
| Monotonicity/congruence | `gcongr` |
| General simplification | `simp` (last resort) |
| Nonlinear arithmetic | `nlinarith [hint]` |
| ℕ subtraction → ℤ | `zify [h1, h2]` |

- **Terminal `simp`**: do NOT squeeze (maintenance burden from lemma renames)
- **Non-terminal `simp`**: MUST be `simp only [...]`
- **One tactic per line** (semicolons only for short single-idea sequences)

### Attributes

- `@[simp]`: equations/iff where LHS is more complex than RHS; must not loop
- `@[ext]`: extensionality lemmas
- `@[simps]`: auto-generate projection simp lemmas for structures
- `@[gcongr]`: congruence lemmas of form `f x₁ ∼ f x₂` given `x₁ ∼ x₂`

### Types and definitions

- **`Type*`** not `Type _` (performance requirement)
- **`where` syntax** for instances, not braces
- **`variable` blocks** for shared parameters — don't repeat `{X : Type*} [Fintype X]`
- **Hypotheses left of colon** — `(h : 1 < n) : 0 < n` not `: 1 < n → 0 < n`
- **`abbrev`** (reducible) requires justification; `@[irreducible]` requires justification
- **Classical by default** — don't thread `Decidable` instances unless the type requires them

### Documentation

- **Module docstring** (`/-! ... -/`) required after imports: title, summary,
  Main definitions, Main statements, Implementation notes, References, Tags
- **Definition docstrings** (`/-- ... -/`) required on every `def` (linter: `docBlame`)
- **References**: cite as `[AuthorYear]`, anchor in `docs/references.bib`

### Imports

- **Granular imports only** — never `import Mathlib`
- Import hierarchy: Algebra → Order → Topology → Analysis (no cross-category violations)
- Files under ~1000 lines; split along natural boundaries

## Aristotle prover

**Role: leaf-lemma grinder and dependency detector, not theorem architect.**

### When to use

- Cast-control lemmas (ℕ → ℝ), positivity/nonzeroness, algebraic reshaping
- Fin arithmetic, decidability, iteration simplification
- High success on algebraic/order-theoretic leaves

### When NOT to use

- Headline theorems, design decisions, anything where definitions are still moving
- If you can't explain in one sentence why the lemma is true, don't submit it

### Submission protocol

1. **Freeze the statement** — hand-design def + statement, compile to sorry, then submit
2. **Each sorry = one leaf** — one concept, one obvious target, short dependency cone
3. **Proof-shaped files** — short helpers first, named intermediates, minimal imports
4. **Batch by type**: positivity → algebra → iteration → decidability → cleanup
5. **`prove_file` with `wait=False`** — runs take minutes to hours; don't poll in tight loops

### Output handling

- Keep the statement, keep discovered dependencies
- **Rewrite proof into clean human-owned form** — Aristotle output is draft, not scripture
- Artifacts go to `docs/aristotle/artifacts/*.lean.txt` (outside build tree)

### Known limitations

- Aristotle runs Lean 4.24.0 — outputs may not compile on our 4.28.0
- Sometimes generates `exact?` (interactive-only tactic) — rewrite manually
- Do NOT use `axiom` to provide upstream lemmas — shadows function definitions

## Hard-won API gotchas

### Nat.cast

- After `Nat.cast_sub`, need `simp only [Nat.cast_ofNat, Nat.cast_one]` to normalize
  `↑2 → 2` and `↑1 → 1` before `linarith` can close
- `exact_mod_cast` resolves `↑n` vs `n` mismatches
- `Nat.cast_pos` for `0 < ↑n ↔ 0 < n`

### Function.iterate

- `Function.iterate_succ_apply'` — `f^[n+1] x = f (f^[n] x)` (unfold from the right)
- `Function.iterate_zero` — `f^[0] x = x`

### Equiv.Perm / Finset.sort

- Core to ordinal pattern extraction — grows during proof work

### Dynamics.PeriodicPts

- `Function.minimalPeriod` — smallest `n > 0` with `f^[n] x = x`
- `Function.IsPeriodicPt` — `f^[n] x = x`
- Uses `Dynamics.PeriodicPts.Defs`, NOT `GroupTheory.OrderOfElement`

### ℕ arithmetic

- `ring` does NOT close `a * a^n = a^(n+1)` on ℕ — use `rw [pow_succ, mul_comm]`
- `zify [h1, h2] at ih ⊢` converts ℕ subtraction to ℤ

## Variable naming

- **Never shadow prelude names**: don't use `le`, `lt`, `eq`, `ne` as variable names
- Standard parameters: `{X : Type*} [Fintype X] [DecidableEq X]`, `(f : X → X)`,
  `(α : X → ℝ)`, `(k : ℕ)` for window length

## File structure

| File | Role | Route | Status |
|------|------|-------|--------|
| `OrdinalPattern.lean` | Bandt-Pompe ordinal pattern map (upstream candidate) | B | Skeleton |
| `DelayWindow.lean` | Delay embedding + SeparatesOrbits + characterization (upstream candidate) | B | Skeleton |
| `IteratePeriod.lean` | Period, orbit, bounds | B | Skeleton |
| `TakensDiscrete.lean` | Future finite-horizon corollaries (skeleton, not frozen) | B | Skeleton |
| `OrdinalTakens.lean` | Ordinal delay compression/quotient theory | B | Skeleton |
| `SardInfra.lean` | Sard axiom typeclass (reference for upstream discussion, not PR-ready) | A | Skeleton |
| `SmoothTakens.lean` | Classical theorem from axiom | A | Skeleton |
| `Verify.lean` | Axiom dashboard (diagnostic, NOT in root aggregator) | Both | Skeleton |

Lean options (`relaxedAutoImplicit`, `autoImplicit`) are set globally in `lakefile.toml`,
not per-file. This is a deliberate divergence from fd/cd (which used redundant per-file
`set_option`). The lakefile is the single source of truth for options.

**Namespace policy**: Upstream candidates target Mathlib namespaces (TBD at gate 3).
Project-local files use no namespace wrapper — deliberate for a terminal research repo.

## Axiom boundary (SardInfra)

`SardInfra` axiomizes only `sard_of_finrank_gt` — the high-dimensional case of Sard's
theorem requiring implicit function theorem + Taylor remainder. The equidimensional
case (`sard_of_finrank_eq`, area formula) and low-dimensional case (`sard_of_finrank_lt`,
Hausdorff dimension) are proved from existing Mathlib infrastructure.

Not meant to be instantiated in this repo — exists to let Route A proofs proceed
under an explicit, auditable axiom boundary. `SmoothTakens.lean` does NOT import
`SardInfra` — its content (embedding chain) is fully axiom-free.

Enforcement levels match the Project section above. Modeled on cd-formalization's
`PDEInfra` pattern.

## Workflow rules

- **No sorries on main** — enforced by CI after gate 1.5
- **Internal docs** (`docs/internal/`) are NOT committed to git
- **Commit messages**: substantive, `<type>: <description>` format
- Feature branches merge to main via fast-forward; delete after merge
- **Mathlib PR process**: post to Zulip first, small PRs preferred, AI disclosure required
