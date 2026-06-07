#!/usr/bin/env python3
"""Static checks for the v28 hard-parts patch.

This script intentionally does not require Lean.  It checks only file presence,
that the experimental umbrella is opt-in, and that the visible D7 relay tables
retain the expected row counts in the source text.
"""
from __future__ import annotations

from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]

REQUIRED = [
    "EvenV11/V28Hard.lean",
    "EvenV11/V28Hard/D3TerminalA2Parametric.lean",
    "EvenV11/LowD5M4RibbonInterface.lean",
    "EvenV11/LowD5M4TameObstruction.lean",
    "EvenV11/V28Hard/D7TwoRailRelay.lean",
    "EvenV11/V28Hard/HighEvenEndpointPromotions.lean",
    "EvenV11/V28Hard/ChecklistFromHardParts.lean",
    "EvenV11/V28Hard/ChecklistH2RootFlat.lean",
    "docs/V28_HARD_PARTS_CODE_NOTES_20260606.md",
    "docs/V28_H2_SKELETON_PLAN_20260607.md",
]


def fail(msg: str) -> None:
    print(f"ERROR: {msg}", file=sys.stderr)
    raise SystemExit(1)


def count_records(block_name: str, text: str) -> int:
    m = re.search(rf"def {block_name}[^:]*:[^=]*:=\n(?P<body>.*?)(?:\n/--|\nstructure|\ntheorem|\ndef |\nend )", text, re.S)
    if not m:
        fail(f"could not locate definition {block_name}")
    return m.group("body").count("{ ")


def main() -> None:
    for rel in REQUIRED:
        path = ROOT / rel
        if not path.exists():
            fail(f"missing {rel}")

    even_v11 = (ROOT / "EvenV11.lean").read_text()
    if "V28Hard" in even_v11:
        fail("EvenV11.lean imports the experimental V28Hard umbrella")

    active_import_text = "\n".join(
        path.read_text()
        for path in (ROOT / "EvenV11/V28Hard").glob("*.lean")
    )
    for token in [
        "EvenV11.LowD5M4H2PaperRow",
        "EvenV11.LowD5M4Realization",
        "EvenV11.V28Hard.D5M4H2Skeleton",
        "EvenV11.V28Hard.D5M4RibbonRows",
        "EvenV11.V28Hard.D7Checkpoint",
        "EvenV11.V28Hard.D7FiniteToCycleData",
    ]:
        if token in active_import_text:
            fail(f"active V28Hard surface imports archived token: {token}")

    d7 = (ROOT / "EvenV11/V28Hard/D7TwoRailRelay.lean").read_text()
    expected = {
        "stageRows": 14,
        "stageSkeletons": 5,
        "colorClosureData": 7,
    }
    for name, want in expected.items():
        got = count_records(name, d7)
        if got != want:
            fail(f"{name}: expected {want} records, found {got}")

    hard_files = list((ROOT / "EvenV11/V28Hard").glob("*.lean"))
    sorry_sites = []
    for path in hard_files:
        for lineno, line in enumerate(path.read_text().splitlines(), 1):
            if re.search(r"\bsorry\b", line):
                stripped = line.strip()
                if stripped.startswith("/-") or stripped.startswith("--") or "`sorry`" in stripped or "`sorry`s" in stripped:
                    continue
                sorry_sites.append(f"{path.relative_to(ROOT)}:{lineno}: {stripped}")
    print("v28 hard-parts static checks passed")
    print(f"tracked hard files: {len(hard_files)}")
    print(f"explicit sorry sites: {len(sorry_sites)}")
    for site in sorry_sites:
        print(f"  {site}")


if __name__ == "__main__":
    main()
