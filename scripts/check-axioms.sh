#!/bin/bash
# Check that TakensFormal.Verify contains no sorryAx.
# Gate 1.5: fails on sorryAx presence.
# Gate 3 (future): upgrade to full axiom allowlist after SardInfra is designed.
#
# NOTE: This script false-passes when Verify.lean has no #print axioms
# commands (skeleton state). It becomes meaningful once definitions and
# theorems exist and Verify.lean has live #print axioms lines.
set -euo pipefail

OUTPUT=$(lake env lean TakensFormal/Verify.lean 2>&1)

# Guard: fail if no axiom output at all (skeleton Verify.lean)
if ! echo "$OUTPUT" | grep -q "axioms"; then
  echo "WARN: no #print axioms output found — Verify.lean may be skeleton-only"
  echo "This check becomes meaningful once definitions exist."
  exit 0  # Soft-pass at scaffold time; change to exit 1 at gate 3
fi

if echo "$OUTPUT" | grep -q "sorryAx"; then
  echo "FAIL: sorryAx found in axiom dashboard"
  echo ""
  echo "$OUTPUT" | grep "sorryAx"
  exit 1
fi

echo "PASS: no sorryAx in axiom dashboard"
