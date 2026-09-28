# Axiom Dashboard

[`Verify.lean`](https://github.com/Project-Navi/takens-formalization/blob/main/TakensFormal/Verify.lean)
contains one `#print axioms` line for each selected declaration: every headline result and
every project declaration these pages cite (229 at present). CI requires exactly one record
per line, in order, and accepts only the three axioms below. This page explains what that
check certifies and what it does not.

## Standard logical axioms

Every selected declaration depends on at most these three axioms of Lean's type theory.
They are not assumptions about dynamical systems.

### `propext` --- propositional extensionality

$$(P \leftrightarrow Q) \;\Longrightarrow\; P = Q$$

Logically equivalent propositions are equal. Rewriting along an "if and only if" uses it.

### `Classical.choice` --- choice

> Every nonempty type has an element.

It gives the law of excluded middle and proof by contradiction, which analysis and
measure theory use throughout.

### `Quot.sound` --- quotient soundness

> Related elements are equal in the quotient.

Quotient types, and with them `Finset`, `Multiset` and function extensionality, rely on it.

## What the check certifies

- **No `sorry`.** An unfinished proof leaves `sorryAx` in the record, which CI rejects.
- **No custom axioms.** No source file declares an `axiom`, and CI rejects any record that
  mentions one, including the axioms behind native evaluation.
- **No assumption classes.** No typeclass or structure carries unproved mathematical
  results as fields; CI rejects `...Infra` classes.
- **Independent replay.** `leanchecker` re-checks every declaration of the library's import
  closure in a fresh kernel.

## What it does not certify

A clean record says the proof is complete relative to the statement. It does not say the
statement's hypotheses hold in a given application. For example, the fixed-map theorem
`ae_isContMDiffEmbedding_delayEmbedding_perturb_of_interpolates` assumes that \(T\) is
injective with injective differentials and has no periodic points of period at most
\(4d\); the [Theorem Catalog](theorems.md) summarizes each statement, and the source gives
it in full.

## Reproducing the check

```bash
lake exe cache get
make build                                   # every module, warnings as errors
python3 scripts/check_axioms.py              # the records, against the allowlist
lake env leanchecker --fresh TakensFormal    # fresh kernel replay
```

`lake env lean TakensFormal/Verify.lean` prints the records themselves, one per line:

```text
'sard' depends on axioms: [propext, Classical.choice, Quot.sound]
```
