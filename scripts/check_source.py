#!/usr/bin/env python3
"""Audit the tracked Lean sources.

Checks, on every tracked `.lean` file:
- no unfinished-proof or trust-extending token in code (comments and strings are skipped,
  so explanatory prose about `sorry` is allowed): `sorry`, `admit`, `sorryAx`,
  `native_decide`, `ofReduceBool`, `trustCompiler`, `implemented_by`, `extern`,
  `unsafe`, `debug.skipKernelTC`, `#exit`, and `axiom` declarations;
- no assumption class or structure named `...Infra`;
- the copyright header, and no bare `import Mathlib`;
- the root `TakensFormal.lean` imports every library module except the diagnostic ones,
  and no library module imports a diagnostic module;
- generic modules (see `GENERIC_PREFIXES`) import only Mathlib and other generic modules.

`--list-modules` prints every tracked module name instead, for `lake build`.
"""
from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

ROOT_MODULE = "TakensFormal"
DIAGNOSTIC_MODULES = {"TakensFormal.Verify", "TakensFormal.Examples"}
# Modules that must not depend on project-specific files (reusable layer).
GENERIC_PREFIXES: tuple[str, ...] = ("TakensFormal.ForMathlib.",)
PROJECT_HEADER = (
    "/-\n"
    "Copyright (c) 2026 Nelson Spence. All rights reserved.\n"
    "Released under Apache 2.0 license as described in the file LICENSE.\n"
)
# Ported third-party files keep their own notice; map path prefix -> required header prefix.
PORTED_HEADERS: dict[str, str] = {}
FORBIDDEN_WORDS = (
    "sorry", "admit", "sorryAx", "native_decide", "ofReduceBool", "trustCompiler",
    "implemented_by", "extern", "unsafe", "skipKernelTC",
)
FORBIDDEN_COMMANDS = ("#exit",)
AXIOM_DECL = re.compile(
    r"(?m)^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|partial|nonrec)\s+)*"
    r"axiom\b"
)
INFRA_DECL = re.compile(r"(?m)^\s*(?:@\[[^\]]*\]\s*)?(?:class|structure)\s+\w*Infra\b")
IMPORT = re.compile(r"(?m)^import\s+(\S+)\s*$")


def strip_comments_and_strings(src: str) -> str:
    """Replace Lean comments and string literals by spaces, keeping line structure."""
    out: list[str] = []
    i, n, depth = 0, len(src), 0
    while i < n:
        if depth == 0 and src.startswith("--", i):
            j = src.find("\n", i)
            j = n if j == -1 else j
            out.append(" " * (j - i))
            i = j
        elif src.startswith("/-", i):
            depth += 1
            out.append("  ")
            i += 2
        elif depth > 0 and src.startswith("-/", i):
            depth -= 1
            out.append("  ")
            i += 2
        elif depth > 0:
            out.append("\n" if src[i] == "\n" else " ")
            i += 1
        elif src[i] == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            segment = src[i:j + 1]
            out.append("".join("\n" if c == "\n" else " " for c in segment))
            i = j + 1
        else:
            out.append(src[i])
            i += 1
    return "".join(out)


def forbidden_tokens(src: str) -> list[str]:
    """Return the forbidden tokens occurring in code (not comments or strings)."""
    code = strip_comments_and_strings(src)
    found = []
    for word in FORBIDDEN_WORDS:
        if re.search(rf"(?<![\w.']){re.escape(word)}(?![\w'])", code):
            found.append(word)
    for command in FORBIDDEN_COMMANDS:
        if re.search(rf"(?m)^\s*{re.escape(command)}\b", code):
            found.append(command)
    if AXIOM_DECL.search(code):
        found.append("axiom declaration")
    if INFRA_DECL.search(code):
        found.append("...Infra class/structure")
    return found


def module_name(path: str) -> str:
    return path[: -len(".lean")].replace("/", ".")


def tracked_lean_files() -> list[str]:
    out = subprocess.run(
        ["git", "ls-files", "*.lean"], capture_output=True, text=True, check=True
    ).stdout
    return sorted(line for line in out.splitlines() if line)


def check_file(path: str, src: str) -> list[str]:
    failures = [f"{path}: forbidden token `{t}`" for t in forbidden_tokens(src)]
    header = next((h for p, h in PORTED_HEADERS.items() if path.startswith(p)), PROJECT_HEADER)
    if not src.startswith(header):
        failures.append(f"{path}: missing or altered copyright header")
    if re.search(r"(?m)^import\s+Mathlib\s*$", src):
        failures.append(f"{path}: bare `import Mathlib` (use granular imports)")
    return failures


def check_imports(sources: dict[str, str]) -> list[str]:
    failures = []
    modules = {module_name(p): src for p, src in sources.items()}
    library = {m for m in modules if m == ROOT_MODULE or m.startswith(ROOT_MODULE + ".")}
    root_imports = set(IMPORT.findall(modules.get(ROOT_MODULE, "")))
    for m in sorted(library - DIAGNOSTIC_MODULES - {ROOT_MODULE}):
        if m not in root_imports:
            failures.append(f"{ROOT_MODULE}.lean does not import library module {m}")
    for m, src in modules.items():
        imports = IMPORT.findall(src)
        if m not in DIAGNOSTIC_MODULES:
            for imp in imports:
                if imp in DIAGNOSTIC_MODULES:
                    failures.append(f"{m} imports diagnostic module {imp}")
        if m.startswith(GENERIC_PREFIXES):
            for imp in imports:
                if imp.startswith(ROOT_MODULE) and not imp.startswith(GENERIC_PREFIXES):
                    failures.append(f"generic module {m} imports project module {imp}")
    return failures


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--list-modules", action="store_true")
    args = parser.parse_args()
    files = tracked_lean_files()
    if args.list_modules:
        print(" ".join(module_name(f) for f in files))
        return 0
    if not files:
        print("SOURCE CHECK FAILED: no tracked Lean files")
        return 1
    sources = {f: Path(f).read_text(encoding="utf-8") for f in files}
    failures = [msg for f, src in sources.items() for msg in check_file(f, src)]
    failures += check_imports(sources)
    if failures:
        print("SOURCE CHECK FAILED:")
        for failure in failures:
            print(f"- {failure}")
        return 1
    print(f"SOURCE CHECK PASSED: {len(files)} tracked Lean files")
    return 0


if __name__ == "__main__":
    sys.exit(main())
