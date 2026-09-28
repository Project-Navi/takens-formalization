#!/bin/bash
# Strict axiom-record check of the declarations selected in TakensFormal/Verify.lean.
# Fails on empty output, missing/duplicate/extra records, Lean errors, or any axiom
# outside [propext, Classical.choice, Quot.sound]. See scripts/check_axioms.py.
set -euo pipefail
exec python3 "$(dirname "$0")/check_axioms.py" "$@"
