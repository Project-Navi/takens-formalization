# Axiom Dashboard

Every declaration in this formalization has been audited via `#print axioms` in
[`Verify.lean`](https://github.com/Project-Navi/takens-formalization/blob/main/TakensFormal/Verify.lean).
This page explains what that audit means.

## Foundational axioms

All 42 declarations depend on exactly three axioms, which are part of
Lean 4's type-theoretic foundation. They are not assumptions about
dynamical systems -- they are logical infrastructure that every
nontrivial Lean proof uses.

### `propext` -- Propositional extensionality

$$
(P \leftrightarrow Q) \;\Longrightarrow\; P = Q
$$

Two propositions that are logically equivalent are equal as terms.
This is the principle that lets Lean treat "if and only if" as
actual equality of propositions, which is needed whenever a proof
rewrites one side of an equivalence for the other.

### `Classical.choice` -- Classical logic

> Every nonempty type has an element.

This axiom provides the law of excluded middle ($P \lor \lnot P$) and
proof by contradiction. It is called "classical" because constructive
mathematics rejects it -- but standard analysis and dynamics rely on it
pervasively (e.g., the existence of a minimum over a nonempty finite
set).

### `Quot.sound` -- Quotient soundness

> Equivalent elements are equal in the quotient type.

If $a \sim b$ under an equivalence relation, then $[a] = [b]$ in the
quotient. This is the axiom that makes quotient types work in Lean's
type theory. It appears in any proof that uses `Finset`, `Multiset`,
or quotient constructions from Mathlib.

## What "zero custom axioms" means

The proofs depend **only** on the three axioms above. There are no
`axiom` declarations in any source file, no `SardInfra` typeclass
postulating unproved results, and no domain-specific assumptions
taken on faith.

In Lean, you can declare an `axiom` to assert any proposition without
proof. Some formalizations use this to defer hard lemmas or bridge
gaps in the library. This formalization does not: every step in every
proof chain is verified down to Lean's kernel.

## What "zero `sorryAx`" means

In Lean, `sorry` is a tactic that closes any goal without proof.
It compiles, but it leaves a marker called `sorryAx` in the axiom
trace. If `#print axioms` for a declaration shows `sorryAx`, that
declaration's proof is incomplete -- there is an unfinished hole
somewhere in its dependency tree.

**No declaration in this formalization shows `sorryAx`.** Every proof
is complete.

## Why this matters

A formal proof is only as strong as its axioms. The guarantee here is:

1. **Soundness** -- the theorems follow from Lean's type theory, which
   has been extensively studied and has multiple independent
   implementations of its kernel.
2. **Completeness** -- there are no holes. Every `sorry` has been
   resolved.
3. **Transparency** -- the exact axiom dependencies are machine-checked
   and displayed. Nothing is hidden.

For a dynamical systems researcher, this means the delay embedding
characterization, the ordinal compression bounds, the Sard measure-zero
results, and the smooth embedding chain are all proved to the same
standard as the most rigorous paper proofs -- except that the checking
is done by a computer, not by a referee.

## Reproducing the audit

```bash
# Build everything (warnings are errors)
lake build --wfail

# Run the axiom dashboard
lake env lean TakensFormal/Verify.lean
```

Every `#print axioms` line will output one of:

- `'declaration' depends on axioms: [propext, Classical.choice, Quot.sound]`
- `'declaration' does not depend on any axioms` (for definitions that are pure computation)

If `sorryAx` or any other axiom appears, the build is unsound.
