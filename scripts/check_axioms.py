#!/usr/bin/env python3
"""Check the `#print axioms` records of the selected declarations.

The selected declarations are the `#print axioms` lines of `TakensFormal/Verify.lean`,
read statically from the source. The file is then elaborated with `lake env lean`, and
its output must contain exactly one record per selected declaration, in source order,
each depending only on the allowlisted axioms. Empty output, missing, duplicate, extra
or renamed records, any error message, and a nonzero Lean exit status are failures.

Usage: python3 scripts/check_axioms.py [--verify-file PATH]
"""
from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

ALLOWED = frozenset({"propext", "Classical.choice", "Quot.sound"})
PRINT_AXIOMS = re.compile(r"^#print axioms\s+(\S+)\s*$")
# `'name' depends on axioms: [a, b]` (the list may wrap across lines) or
# `'name' does not depend on any axioms`, optionally after a `file:line:col: info:` prefix.
RECORD = re.compile(
    r"'(?P<name>[^\n]+?)'\s+(?:depends on axioms:\s*\[(?P<axioms>[^\]]*)\]"
    r"|(?P<none>does not depend on any axioms))"
)
# Lean reports errors as `path:line:col: error: ...` (or a bare `error: ...`).
ERROR = re.compile(r"(?m)^(?:\S*:\d+:\d+:\s*)?error\b")


def expected_names(verify_source: str) -> list[str]:
    """Return the declarations selected by `#print axioms` lines, in order."""
    names = []
    for line in verify_source.splitlines():
        match = PRINT_AXIOMS.match(line.strip())
        if match:
            names.append(match.group(1))
    return names


def parse_records(output: str) -> list[tuple[str, list[str]]]:
    """Parse every axiom record in Lean's output."""
    records = []
    for match in RECORD.finditer(output):
        axioms = [] if match.group("none") else [
            a.strip() for a in match.group("axioms").replace("\n", " ").split(",") if a.strip()
        ]
        records.append((match.group("name"), axioms))
    return records


def validate(expected: list[str], output: str, returncode: int) -> list[str]:
    """Return a list of failures; an empty list means the records are acceptable."""
    failures = []
    if returncode != 0:
        failures.append(f"Lean exited with status {returncode}")
    if ERROR.search(output):
        failures.append("Lean output contains an error message")
    if not expected:
        failures.append("no `#print axioms` lines were selected")
    duplicates = sorted({n for n in expected if expected.count(n) > 1})
    if duplicates:
        failures.append(f"duplicate selected declarations: {duplicates}")
    records = parse_records(output)
    if not records:
        failures.append("no axiom records in Lean output")
    names = [name for name, _ in records]
    if names != expected:
        missing = [n for n in expected if n not in names]
        extra = [n for n in names if n not in expected]
        repeated = sorted({n for n in names if names.count(n) > 1})
        failures.append(
            "records do not match the selected declarations one-to-one in order "
            f"(expected {len(expected)}, got {len(names)}; missing={missing}, "
            f"extra={extra}, repeated={repeated})"
        )
    for name, axioms in records:
        bad = sorted(set(axioms) - ALLOWED)
        if bad:
            failures.append(f"{name} depends on non-allowlisted axioms {bad}")
    return failures


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verify-file", default="TakensFormal/Verify.lean")
    args = parser.parse_args()
    verify = Path(args.verify_file)
    expected = expected_names(verify.read_text(encoding="utf-8"))
    proc = subprocess.run(
        ["lake", "env", "lean", str(verify)], capture_output=True, text=True, check=False
    )
    output = proc.stdout + proc.stderr
    failures = validate(expected, output, proc.returncode)
    if failures:
        print(output)
        print("AXIOM CHECK FAILED:")
        for failure in failures:
            print(f"- {failure}")
        return 1
    print(f"AXIOM CHECK PASSED: {len(expected)} records, each within {sorted(ALLOWED)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
