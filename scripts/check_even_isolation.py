#!/usr/bin/env python3
"""Isolation checks for the even-modulus formalization.

Fails (exit 1) when any of the following holds:
  1. a file under TorusEven/ imports TorusEvenAttic, RoundComposite.OddCore,
     RoundComposite.PrefixCount*, RoundComposite.ActiveHall, or any file
     outside the allowed prefixes (Shared., TorusEven., D5Odd.EvenRouteEM4,
     D5Odd.EvenLambdaE, Mathlib);
  2. a Lean file under TorusEven/, TorusEvenAttic/, or the D5Odd even leaf
     lacks a first-line `-- STATUS:` header;
  3. any tracked Lean source contains `sorry`, `admit`, an author `axiom`, or
     `constant`;
  4. `native_decide` appears in a TorusEven/ file, or in a registered leaf
     file that is not in NATIVE_DECIDE_LEAVES.
The registry is the single place where trusted native leaves are listed.
"""
from __future__ import annotations
import re, sys, subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MAIN = ROOT / "TorusEven"
ATTIC = ROOT / "TorusEvenAttic"
ALLOWED_IMPORT_PREFIXES = ("Shared.", "TorusEven.", "Mathlib",
                           "D5Odd.EvenRouteEM4", "D5Odd.EvenLambdaE")
FORBIDDEN_IMPORT_PREFIXES = ("TorusEvenAttic", "RoundComposite.OddCore",
                             "RoundComposite.PrefixCount", "RoundComposite.ActiveHall",
                             "RoundComposite.V75Endpoints")
STATUS_RE = re.compile(r"^-- STATUS: (main-path|conditional|evidence|attic)\b")
# Files whose native_decide use is accepted as a trusted finite leaf for the even path.
NATIVE_DECIDE_LEAVES = {
    "D5Odd/EvenRouteEM4.lean": "D_5(4) schedule: exact cover, Latin, rank tables (ZMod 256)",
    "D5Odd/EvenLambdaE.lean": "Lambda_E row table: bijectivity and cyclic shift",
}
STATUS_REQUIRED = [MAIN, ATTIC, ROOT / "D5Odd" / "EvenRouteEM4.lean",
                   ROOT / "D5Odd" / "EvenLambdaE.lean"]

def strip_comments(text: str) -> str:
    """Remove `--` line comments and `/- ... -/` block comments (nesting ignored)."""
    text = re.sub(r"/-.*?-/", "", text, flags=re.S)
    return "\n".join(line.split("--", 1)[0] for line in text.splitlines())

def tracked_lean() -> list[Path]:
    out = subprocess.run(["git", "ls-files", "*.lean"], cwd=ROOT,
                         capture_output=True, text=True, check=True).stdout.split()
    files = [ROOT / f for f in out]
    # include untracked-but-present new files in the even trees
    for d in (MAIN, ATTIC):
        files += [p for p in d.rglob("*.lean") if p not in files]
    return sorted(set(files))

def lean_files_under(p: Path) -> list[Path]:
    return [p] if p.is_file() else sorted(p.rglob("*.lean"))

def main() -> int:
    problems: list[str] = []
    # 1. import boundary
    for f in lean_files_under(MAIN):
        for line in f.read_text().splitlines():
            m = re.match(r"^import\s+(\S+)", line)
            if not m: continue
            mod = m.group(1)
            if mod.startswith(FORBIDDEN_IMPORT_PREFIXES) or not mod.startswith(ALLOWED_IMPORT_PREFIXES):
                problems.append(f"{f.relative_to(ROOT)}: forbidden import {mod}")
    # 2. STATUS headers
    for p in STATUS_REQUIRED:
        for f in lean_files_under(p):
            first = f.read_text().splitlines()[0] if f.read_text() else ""
            if not STATUS_RE.match(first):
                problems.append(f"{f.relative_to(ROOT)}: missing `-- STATUS:` header")
    # 3. sorry / admit / axiom / constant
    bad = re.compile(r"^\s*(axiom|constant)\s|\bsorry\b|\badmit\b")
    for f in tracked_lean():
        for i, line in enumerate(strip_comments(f.read_text()).splitlines(), 1):
            if bad.search(line):
                problems.append(f"{f.relative_to(ROOT)}:{i}: {line.strip()[:60]}")
    # 4. native_decide placement
    for f in lean_files_under(MAIN):
        if re.search(r"\bnative_decide\b", strip_comments(f.read_text())):
            problems.append(f"{f.relative_to(ROOT)}: native_decide is not allowed on the even main path")
    for rel in NATIVE_DECIDE_LEAVES:
        f = ROOT / rel
        if not f.exists():
            problems.append(f"registered leaf missing: {rel}")
    if problems:
        print("EVEN ISOLATION CHECK FAILED")
        for p in problems: print("  " + p)
        return 1
    print("even isolation check passed:",
          f"{len(lean_files_under(MAIN))} main-path files,",
          f"{len(lean_files_under(ATTIC))} attic files,",
          f"{len(NATIVE_DECIDE_LEAVES)} registered native_decide leaves")
    return 0

if __name__ == "__main__":
    sys.exit(main())
