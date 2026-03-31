# Quickstart

Build and verify the formalization locally.

## Prerequisites

- [elan](https://github.com/leanprover/elan) (Lean version manager)
- Git

## Clone and build

```bash
git clone https://github.com/Project-Navi/takens-formalization.git
cd takens-formalization
```

Fetch the Mathlib precompiled cache (saves significant build time):

```bash
lake exe cache get
```

Build with warnings-as-errors --- this is the primary check that enforces zero
sorry:

```bash
lake build --wfail
```

## Verify

Run the Mathlib linter suite:

```bash
lake lint
```

Build the axiom dashboard (diagnostic target, not part of the library):

```bash
lake build TakensFormal.Verify
```

Confirm no `sorryAx` in any declaration:

```bash
lake env lean TakensFormal/Verify.lean 2>&1 | grep -c sorryAx
# Expected output: 0
```

## Toolchain

This project uses Lean 4.28.0 and Mathlib v4.28.0. The toolchain is pinned in
`lean-toolchain` and the Mathlib revision in `lakefile.toml`. No local Mathlib
fork --- the `rev` field is treated as an audit gate.
