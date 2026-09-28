# Quickstart

Build and verify the formalization locally.

## Prerequisites

- [elan](https://github.com/leanprover/elan) (Lean version manager)
- Git, Python 3 and GNU Make

## Clone and build

```bash
git clone https://github.com/Project-Navi/takens-formalization.git
cd takens-formalization
lake exe cache get      # Mathlib's precompiled oleans; never build Mathlib
make build              # every tracked module, warnings are errors
```

## Verify

```bash
make lint               # Mathlib's environment linters
make audit              # source hygiene: no sorry, axiom or assumption class
make verify             # axiom records, documented names, fresh kernel replay
make test-checkers      # negative tests of the checkers
lake env lean -DwarningAsError=true TakensFormal/Examples.lean   # worked examples
```

`make verify` runs `scripts/check_axioms.py`, which accepts a declaration only if it depends
on nothing beyond `propext`, `Classical.choice` and `Quot.sound`; see the
[Axiom Dashboard](../reference/axiom-dashboard.md).

## Documentation

```bash
make docs-check         # build the site and check its links and fragments
make docs-serve         # serve it locally
```

## Toolchain

Lean 4.34.1 and Mathlib v4.34.1, pinned in `lean-toolchain`, `lakefile.toml` and
`lake-manifest.json`. `AGENTS.md` records the conventions and the checks CI runs.
