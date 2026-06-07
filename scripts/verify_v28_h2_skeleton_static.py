#!/usr/bin/env python3
"""Static checks for the active v28 H2 interface.

This does not call Lean.  It checks that the archive-dependent H2 skeleton is no
longer in the active build surface and that the active H2 target is the physical
row/ribbon interface.
"""
from __future__ import annotations

from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]

REQUIRED = [
    "EvenV11/LowD5M4RibbonInterface.lean",
    "EvenV11/LowD5M4TameObstruction.lean",
    "EvenV11/V28Hard/ChecklistH2RootFlat.lean",
    "EvenV11/V28Hard/ChecklistFromHardParts.lean",
    "docs/V28_H2_SKELETON_PLAN_20260607.md",
]

H2_TOKENS = [
    "structure PhysicalLayerRows",
    "structure PhysicalRowsSingletonSwitchMapConjInput",
    "PhysicalRowsSingletonSwitchMapConjInput.nonemptyRibbonData",
    "PhysicalRowsReturnMapConjGoal",
    "PhysicalSingletonSwitchLayerData",
    "physicalRowsLayerBijective_of_singletonSwitchLayerData",
    "returnRealization_of_returnMap_conj",
]

OBSTRUCTION_TOKENS = [
    "tameSeedRootEquiv",
    "no_four_rootSteps_to_tamePaperReturn_color0",
    "not_returnMapConj_tameSeedRootEquiv",
]


def fail(msg: str) -> None:
    print(f"ERROR: {msg}", file=sys.stderr)
    raise SystemExit(1)


def main() -> None:
    for rel in REQUIRED:
        if not (ROOT / rel).exists():
            fail(f"missing {rel}")

    even_v11 = (ROOT / "EvenV11.lean").read_text()
    if "V28Hard" in even_v11:
        fail("EvenV11.lean imports experimental V28Hard modules")

    umbrella = (ROOT / "EvenV11/V28Hard.lean").read_text()
    if "import EvenV11.V28Hard.D7FiniteToCycleData" in umbrella:
        fail("V28Hard umbrella imports D7FiniteToCycleData directly")

    archived = [
        "archive/EvenV11/V28Hard/D5M4RibbonRows.lean",
        "archive/EvenV11/V28Hard/D5M4H2Skeleton.lean",
        "archive/EvenV11/V28Hard/D5M4H2PaperRows.lean",
        "archive/EvenV11/V28Hard/D7Checkpoint.lean",
        "archive/EvenV11/V28Hard/D7FiniteToCycleData.lean",
    ]
    for rel in archived:
        if not (ROOT / rel).exists():
            fail(f"archived stale target missing: {rel}")

    active_import_text = "\n".join(
        path.read_text()
        for path in (ROOT / "EvenV11/V28Hard").glob("*.lean")
    )
    forbidden_imports = [
        "EvenV11.LowD5M4H2PaperRow",
        "EvenV11.LowD5M4Realization",
        "EvenV11.V28Hard.D5M4H2Skeleton",
        "EvenV11.V28Hard.D5M4RibbonRows",
        "EvenV11.V28Hard.D7Checkpoint",
        "EvenV11.V28Hard.D7FiniteToCycleData",
    ]
    for token in forbidden_imports:
        if token in active_import_text:
            fail(f"active V28Hard surface still imports archived token: {token}")

    h2 = (ROOT / "EvenV11/LowD5M4RibbonInterface.lean").read_text()
    for token in H2_TOKENS:
        if token not in h2:
            fail(f"active H2 interface token missing: {token}")

    obstruction = (ROOT / "EvenV11/LowD5M4TameObstruction.lean").read_text()
    for token in OBSTRUCTION_TOKENS:
        if token not in obstruction:
            fail(f"H2 tame obstruction token missing: {token}")

    new_files = [ROOT / rel for rel in REQUIRED if rel.endswith(".lean")]
    bad_sorry = []
    for path in new_files:
        for lineno, line in enumerate(path.read_text().splitlines(), 1):
            if re.search(r"\bsorry\b", line):
                stripped = line.strip()
                if stripped.startswith("--") or stripped.startswith("/-") or "`sorry`" in stripped:
                    continue
                bad_sorry.append(f"{path.relative_to(ROOT)}:{lineno}: {stripped}")
    if bad_sorry:
        fail("unexpected sorry in new skeleton files:\n" + "\n".join(bad_sorry))

    print("active v28 H2 interface static checks passed")
    print(f"required files: {len(REQUIRED)}")
    print(f"active H2 tokens: {len(H2_TOKENS)}")
    print(f"tame obstruction tokens: {len(OBSTRUCTION_TOKENS)}")
    print("archive-dependent H2/D7 checkpoint files are quarantined under archive/")


if __name__ == "__main__":
    main()
