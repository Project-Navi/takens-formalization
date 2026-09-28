#!/usr/bin/env python3
"""Check that the Lean names cited in README.md and docs/ resolve.

Candidates are every inline code span that looks like a Lean identifier, the names in
`theorem-name` labels, and the declarations and `#print axioms`/`#check` targets in
fenced `lean` blocks. Each candidate must either be a tracked module (short or full
name), appear in `IGNORED` (code-formatted words that are not declarations), or resolve
to a declaration when elaborated against `import TakensFormal`. A resolved name defined
in a `TakensFormal` module must also be selected in `TakensFormal/Verify.lean`, so every
project declaration the docs cite is covered by the axiom check.

Usage: python3 scripts/check_doc_names.py
"""
from __future__ import annotations

import re
import subprocess
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_axioms import expected_names  # noqa: E402

IDENT = re.compile(r"^[A-Za-z_Ͱ-Ͽ][\w'.]*[\w']$|^[A-Za-z]$")
FILE_SUFFIXES = (".lean", ".md", ".toml", ".json", ".yml", ".yaml", ".sh", ".py", ".svg")
# Namespaces tried when a cited name is not fully qualified.
OPEN_NAMESPACES = ("", "Function.", "MeasureTheory.", "MeasureTheory.Measure.", "Set.")
# Code-formatted words in the docs that are not Lean declarations.
IGNORED = {
    "sorry", "axiom", "lake", "elan", "uv", "rev", "main", "leanchecker", "zensical",
    "noncomputable", "by", "where",
    # tactics
    "aesop", "decide", "omega", "simp", "grind", "norm_num", "positivity", "gcongr", "ring",
    "linarith", "nlinarith", "field_simp", "zify", "push_cast", "exact_mod_cast", "fun_prop",
}
DECL = re.compile(
    r"(?m)^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable)\s+)*"
    r"(?:theorem|lemma|def|abbrev|structure|class|instance|inductive)\s+([^\s(:{\[]+)"
)
COMMAND = re.compile(r"(?m)^\s*#(?:print axioms|check)\s+@?([^\s]+)")
FENCE = re.compile(r"(?ms)^```(\w*)\n(.*?)^```")
THEOREM_LABEL = re.compile(r'class="theorem-name">\(([^)<\s]+)')


def markdown_files() -> list[Path]:
    out = subprocess.run(
        ["git", "ls-files", "README.md", "docs/*.md", "docs/**/*.md"],
        capture_output=True, text=True, check=True,
    ).stdout
    return sorted({Path(p) for p in out.splitlines() if p})


def candidates(text: str) -> set[str]:
    found: set[str] = set()
    for lang, body in FENCE.findall(text):
        if lang == "lean":
            found.update(DECL.findall(body))
            found.update(COMMAND.findall(body))
    prose = FENCE.sub("", text)
    for span in re.findall(r"`([^`\n]+)`", prose):
        span = span.strip()
        if IDENT.match(span) and not span.endswith(FILE_SUFFIXES):
            found.add(span)
    found.update(THEOREM_LABEL.findall(text))
    return found


def mathlib_module_exists(name: str) -> bool:
    """Whether `Mathlib.X.Y` is a module of the pinned Mathlib checkout."""
    return (Path(".lake/packages/mathlib") / (name.replace(".", "/") + ".lean")).is_file()


def classify(names: set[str], modules: set[str]) -> tuple[set[str], set[str], list[str]]:
    """Split names into (to_resolve, skipped, failures for bad module paths)."""
    short_modules = {m.rsplit(".", 1)[-1] for m in modules}
    skipped = {
        n for n in names
        if n in IGNORED or n in modules or n in short_modules or len(n) <= 2
    }
    module_paths = {n for n in names - skipped if n.startswith("Mathlib.")}
    failures = [f"`{n}` is not a module of the pinned Mathlib"
                for n in sorted(module_paths) if not mathlib_module_exists(n)]
    return names - skipped - module_paths, skipped | module_paths, failures


def resolve(names: list[str]) -> tuple[dict[str, tuple[str, str]], list[str], str]:
    """Resolve names with Lean. Returns (name -> (full name, module), missing, raw output)."""
    quoted = ", ".join(f'"{n}"' for n in names)
    prefixes = ", ".join(f'"{p}"' for p in OPEN_NAMESPACES)
    program = f"""import TakensFormal
open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  for s in [{quoted}] do
    let mut found := false
    for p in [{prefixes}] do
      let n := (p ++ s).toName
      if !found && env.contains n then
        found := true
        let m := match env.getModuleIdxFor? n with
          | some i => (env.header.moduleNames[i.toNat]!).toString
          | none => "<current>"
        IO.println s!"RESOLVED {{s}} {{n}} {{m}}"
    if !found && env.isNamespace s.toName then
      found := true
      IO.println s!"RESOLVED {{s}} {{s}} <namespace>"
    if !found then
      IO.println s!"MISSING {{s}}"
"""
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp) / "DocNames.lean"
        path.write_text(program, encoding="utf-8")
        proc = subprocess.run(
            ["lake", "env", "lean", str(path)], capture_output=True, text=True, check=False
        )
    output = proc.stdout + proc.stderr
    if proc.returncode != 0:
        raise RuntimeError(f"Lean exited with status {proc.returncode}:\n{output}")
    resolved, missing = {}, []
    for line in output.splitlines():
        parts = line.split()
        if len(parts) == 4 and parts[0] == "RESOLVED":
            resolved[parts[1]] = (parts[2], parts[3])
        elif len(parts) == 2 and parts[0] == "MISSING":
            missing.append(parts[1])
    if len(resolved) + len(missing) != len(names):
        raise RuntimeError(f"expected {len(names)} resolution lines:\n{output}")
    return resolved, missing, output


def main() -> int:
    tracked = subprocess.run(
        ["git", "ls-files", "*.lean"], capture_output=True, text=True, check=True
    ).stdout.split()
    modules = {p[: -len(".lean")].replace("/", ".") for p in tracked}
    cited: dict[str, set[str]] = {}
    for md in markdown_files():
        for name in candidates(md.read_text(encoding="utf-8")):
            cited.setdefault(name, set()).add(str(md))
    to_resolve, skipped, failures = classify(set(cited), modules)
    resolved, missing, _ = resolve(sorted(to_resolve))
    selected = set(expected_names(Path("TakensFormal/Verify.lean").read_text(encoding="utf-8")))
    failures += [f"`{n}` does not resolve (cited in {sorted(cited[n])})" for n in missing]
    for name, (full, module) in sorted(resolved.items()):
        if module.startswith("TakensFormal") and full not in selected:
            failures.append(
                f"project declaration `{full}` is cited in {sorted(cited[name])} "
                "but not selected in TakensFormal/Verify.lean"
            )
    if failures:
        print("DOC NAME CHECK FAILED:")
        for failure in failures:
            print(f"- {failure}")
        return 1
    print(
        f"DOC NAME CHECK PASSED: {len(resolved)} cited names resolve "
        f"({sum(1 for _, m in resolved.values() if m.startswith('TakensFormal'))} project "
        f"declarations, all selected in Verify.lean); {len(skipped)} non-declaration spans skipped"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
