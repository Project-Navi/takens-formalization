#!/usr/bin/env python3
"""Negative and positive tests for the verification checkers.

Every fixture lives in a temporary directory; nothing here is a committed placeholder.
With `--lean`, the axiom and doc-name checkers are also exercised end to end through
`lake env lean` on temporary files (a `sorry`, a custom axiom, an unknown name, a failing
Lean process); this requires the project to be built.

Usage: python3 scripts/test_checkers.py [--lean]
"""
from __future__ import annotations

import argparse
import contextlib
import os
import subprocess
import sys
import tempfile
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPTS))
import check_axioms  # noqa: E402
import check_doc_names  # noqa: E402
import check_docs_site  # noqa: E402
import check_source  # noqa: E402

RESULTS: list[tuple[str, bool]] = []
STD = "[propext, Classical.choice, Quot.sound]"


def expect(name: str, condition: bool) -> None:
    RESULTS.append((name, condition))
    print(f"{'PASS' if condition else 'FAIL'}: {name}")


def axioms_ok(expected: list[str], output: str, rc: int = 0) -> bool:
    return not check_axioms.validate(expected, output, rc)


def test_axiom_parser() -> None:
    good = f"'a' depends on axioms: {STD}\n'b' does not depend on any axioms\n"
    expect("axioms: expected output accepted", axioms_ok(["a", "b"], good))
    wrapped = "'a' depends on axioms: [propext,\n  Classical.choice,\n  Quot.sound]\n"
    expect("axioms: wrapped record accepted", axioms_ok(["a"], wrapped))
    prefixed = f"info: TakensFormal/Verify.lean:3:0: 'x.y' depends on axioms: {STD}\n"
    expect("axioms: position-prefixed record accepted", axioms_ok(["x.y"], prefixed))
    primed = f"'f'' depends on axioms: {STD}\n"
    expect("axioms: primed name accepted", axioms_ok(["f'"], primed))
    expect("axioms: empty output rejected", not axioms_ok(["a"], ""))
    expect("axioms: no selection rejected", not axioms_ok([], good))
    expect("axioms: wrong names with same count rejected",
           not axioms_ok(["a", "c"], good))
    expect("axioms: reordered records rejected", not axioms_ok(["b", "a"], good))
    dup = f"'a' depends on axioms: {STD}\n'a' depends on axioms: {STD}\n"
    expect("axioms: duplicate record rejected", not axioms_ok(["a"], dup))
    expect("axioms: duplicate selection rejected", not axioms_ok(["a", "a"], dup))
    expect("axioms: missing record rejected", not axioms_ok(["a", "b", "c"], good))
    expect("axioms: extra record rejected", not axioms_ok(["a"], good))
    sorry_out = "'a' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]\n"
    expect("axioms: sorryAx rejected", not axioms_ok(["a"], sorry_out))
    custom = "'a' depends on axioms: [propext, myAxiom]\n"
    expect("axioms: custom axiom rejected", not axioms_ok(["a"], custom))
    native = "'a' depends on axioms: [Lean.ofReduceBool]\n"
    expect("axioms: native evaluation axiom rejected", not axioms_ok(["a"], native))
    expect("axioms: failing Lean process rejected", not axioms_ok(["a", "b"], good, rc=1))
    err = good + "Verify.lean:9:0: error: unknown constant 'z'\n"
    expect("axioms: error message rejected", not axioms_ok(["a", "b"], err))
    src = "#print axioms a\n-- #print axioms commented\n  #print axioms b\n"
    expect("axioms: selection read from source",
           check_axioms.expected_names(src) == ["a", "b"])


HEADER = check_source.PROJECT_HEADER + "Authors: Test\n-/\n"


def source_failures(body: str, header: str = HEADER, path: str = "TakensFormal/X.lean") -> list:
    return check_source.check_file(path, header + body)


def test_source_checker() -> None:
    expect("source: clean file accepted",
           not source_failures("theorem t : True := trivial\n"))
    prose = ("/-- This docstring says no `sorry` is used. -/\ntheorem t : True := trivial\n"
             "-- a comment mentioning sorry and axiom\n/- nested /- sorry -/ -/\n"
             "def s : String := \"sorry\"\n")
    expect("source: explanatory prose and strings accepted", not source_failures(prose))
    for label, body in [
        ("sorry", "theorem t : False := by sorry\n"),
        ("sorry term", "theorem t : False := sorry\n"),
        ("admit", "theorem t : False := by admit\n"),
        ("axiom", "axiom bad : False\n"),
        ("private axiom", "private axiom bad : False\n"),
        ("native_decide", "theorem t : 1 = 1 := by native_decide\n"),
        ("#exit", "theorem t : True := trivial\n#exit\n"),
        ("implemented_by", "@[implemented_by id] def f (n : Nat) : Nat := n\n"),
        ("Infra class", "class SardInfra : Prop where\n  sard : False\n"),
        ("Infra structure", "structure PDEInfra where\n  h : False\n"),
    ]:
        expect(f"source: {label} rejected", bool(source_failures(body)))
    expect("source: missing header rejected",
           bool(check_source.check_file("TakensFormal/X.lean", "theorem t : True := trivial\n")))
    expect("source: bare import Mathlib rejected", bool(source_failures("import Mathlib\n")))
    root = HEADER + "import TakensFormal.A\n"
    mods = {"TakensFormal.lean": root, "TakensFormal/A.lean": HEADER,
            "TakensFormal/B.lean": HEADER, "TakensFormal/Verify.lean": HEADER}
    expect("source: module missing from root rejected", bool(check_source.check_imports(mods)))
    mods_ok = dict(mods, **{"TakensFormal.lean": root + "import TakensFormal.B\n"})
    expect("source: complete root accepted", not check_source.check_imports(mods_ok))
    bad_diag = dict(mods_ok, **{"TakensFormal/B.lean": HEADER + "import TakensFormal.Verify\n"})
    expect("source: library importing diagnostic rejected",
           bool(check_source.check_imports(bad_diag)))
    generic = dict(mods_ok, **{
        "TakensFormal/ForMathlib/G.lean": HEADER + "import TakensFormal.A\n",
        "TakensFormal.lean": root + "import TakensFormal.B\nimport TakensFormal.ForMathlib.G\n"})
    expect("source: generic module importing project module rejected",
           bool(check_source.check_imports(generic)))


def test_doc_candidates() -> None:
    text = ("Use `delayEmbedding` and `Function.minimalPeriod` in `DelayWindow.lean`;"
            " run `lake build`.\n```lean\ntheorem foo_bar (x : Nat) : x = x := rfl\n"
            "#print axioms baz\n```\n<span class=\"theorem-name\">(quxName)</span>\n")
    found = check_doc_names.candidates(text)
    expect("doc names: inline, fenced, #print and label names found",
           {"delayEmbedding", "Function.minimalPeriod", "foo_bar", "baz", "quxName"} <= found)
    expect("doc names: prose labels are not names",
           "high-dimensional" not in check_doc_names.candidates(
               '<span class="theorem-name">(high-dimensional case)</span>'))
    expect("doc names: file names and commands skipped",
           "DelayWindow.lean" not in found and "lake build" not in found)
    to_resolve, skipped, failures = check_doc_names.classify(
        {"DelayWindow", "delayEmbedding", "sorry", "Mathlib.Not.A.Real.Module"},
        {"TakensFormal.DelayWindow"})
    expect("doc names: module and ignored words skipped, names kept",
           to_resolve == {"delayEmbedding"} and {"DelayWindow", "sorry"} <= skipped)
    expect("doc names: nonexistent Mathlib module rejected", bool(failures))


@contextlib.contextmanager
def chdir(path: Path):
    old = Path.cwd()
    os.chdir(path)
    try:
        yield
    finally:
        os.chdir(old)


def run_site_check(pages: dict[str, str], nav: str) -> int:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        (root / "zensical.toml").write_text(
            f'[project]\nsite_url = "https://example.invalid/x"\nnav = [{nav}]\n')
        for route in ("index.md", "a.md"):
            (root / "docs" / route).parent.mkdir(parents=True, exist_ok=True)
            (root / "docs" / route).write_text("# page\n")
        for asset in check_docs_site.EXPECTED_ASSETS:
            (root / "site" / asset).parent.mkdir(parents=True, exist_ok=True)
            (root / "site" / asset).write_text("x")
        for rel, body in pages.items():
            (root / "site" / rel).parent.mkdir(parents=True, exist_ok=True)
            (root / "site" / rel).write_text(body)
        with chdir(root), contextlib.redirect_stdout(open(os.devnull, "w")):
            sys.argv = ["check_docs_site.py"]
            return check_docs_site.main()


def test_site_checker() -> None:
    nav = '{"Home" = "index.md"}, {"A" = "a.md"}'
    good = {"index.html": '<a href="a/#sec">A</a>', "a/index.html": '<h2 id="sec">S</h2>'}
    expect("site: valid site accepted", run_site_check(good, nav) == 0)
    expect("site: broken local link rejected",
           run_site_check(dict(good, **{"index.html": '<a href="b/">B</a>'}), nav) != 0)
    expect("site: missing fragment rejected",
           run_site_check(dict(good, **{"index.html": '<a href="a/#nope">A</a>'}), nav) != 0)
    expect("site: unbuilt nav page rejected",
           run_site_check({"index.html": "<p>x</p>"}, nav) != 0)
    expect("site: retired path rejected",
           run_site_check(dict(good, **{"a/index.html": '<h2 id="sec">debt.md</h2>'}), nav) != 0)


def lean(path: Path) -> subprocess.CompletedProcess:
    return subprocess.run(["lake", "env", "lean", str(path)],
                          capture_output=True, text=True, check=False)


def test_lean_end_to_end() -> None:
    cases = {
        "accepts standard axioms": (
            "theorem good (p : Prop) : p ∨ ¬p := Classical.em p\n#print axioms good\n", True),
        "rejects sorry": ("theorem bad : False := sorry\n#print axioms bad\n", False),
        "rejects a custom axiom": (
            "axiom ax : False\ntheorem bad : False := ax\n#print axioms bad\n", False),
        "rejects a failing Lean process": ("#print axioms doesNotExist\n", False),
    }
    for label, (src, ok) in cases.items():
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "Fixture.lean"
            path.write_text(src)
            proc = lean(path)
            verdict = not check_axioms.validate(
                check_axioms.expected_names(src), proc.stdout + proc.stderr, proc.returncode)
            expect(f"lean e2e: axiom checker {label}", verdict == ok)
    resolved, missing, _ = check_doc_names.resolve(
        ["delayEmbedding", "Function.minimalPeriod", "definitelyNotADeclaration_xyz"])
    expect("lean e2e: doc names resolve project and Mathlib names",
           set(resolved) == {"delayEmbedding", "Function.minimalPeriod"})
    expect("lean e2e: doc names report an unknown name",
           missing == ["definitelyNotADeclaration_xyz"])


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", action="store_true", help="also run Lean end-to-end tests")
    args = parser.parse_args()
    test_axiom_parser()
    test_source_checker()
    test_doc_candidates()
    test_site_checker()
    if args.lean:
        test_lean_end_to_end()
    failed = [name for name, ok in RESULTS if not ok]
    print(f"{len(RESULTS) - len(failed)}/{len(RESULTS)} checker tests passed")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
