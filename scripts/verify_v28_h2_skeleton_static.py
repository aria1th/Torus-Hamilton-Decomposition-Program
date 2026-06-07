#!/usr/bin/env python3
"""Static checks for the v28 H2 skeleton patch.

This does not call Lean.  It checks that the new H2/D7 staging files are present,
that D7 finite-backed use is quarantined behind `D7Checkpoint`, and that the H2
skeleton exposes the intended route names.
"""
from __future__ import annotations

from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]

REQUIRED = [
    "EvenV11/V28Hard/D7Checkpoint.lean",
    "EvenV11/V28Hard/D5M4H2Skeleton.lean",
    "EvenV11/V28Hard/D5M4H2PaperRows.lean",
    "EvenV11/V28Hard/ChecklistH2RootFlat.lean",
    "docs/V28_H2_SKELETON_PLAN_20260607.md",
]

H2_TOKENS = [
    "structure PaperLayeredBaseRows",
    "structure PaperRowReadPieces",
    "structure H2PathRouteSkeleton",
    "structure H2SkewProductPathRouteSkeleton",
    "structure H2CoreYFirstZFirstRouteSkeleton",
    "structure H2SkewProductCoreYFirstZFirstRouteSkeleton",
    "H2PathRouteSkeleton.toRowEquivRibbonData",
    "H2SkewProductPathRouteSkeleton.nonemptyRibbonData",
    "H2SkewProductCoreYFirstZFirstRouteSkeleton.nonemptyRibbonData",
    "H2SkewProductCoreYFirstZFirstRouteSkeleton.nonemptyRibbonData_ofPaperData",
    "not_terminalCoreTailPrefixPathGoal",
    "not_nonempty_resetPortH2PaperSkewProductCoreYFirstZFirstTailData",
    "structure H2TableRouteSkeleton",
    "structure H2RootFlatRouteSkeleton",
    "structure H2RibbonCollapseInput",
    "H2RibbonCollapseInput.toResetPortBaseRowData",
    "structure PaperRowsDirectRibbonCollapseInput",
    "PaperRowsDirectRibbonCollapseInput.nonemptyRibbonData",
    "PaperRowsDirectRibbonCollapseInput.lowBaseFamily",
    "structure PaperPhysicalSingletonSwitchLayerData",
    "structure PaperRowsSingletonDirectRibbonCollapseInput",
    "PaperRowsSingletonDirectRibbonCollapseInput.lowBaseFamily",
    "PaperPhysicalRowsPathRealizationGoal",
    "structure PaperRowsDirectPathRibbonCollapseInput",
    "structure PaperRowsSingletonDirectPathRibbonCollapseInput",
    "PaperRowsSingletonDirectPathRibbonCollapseInput.lowBaseFamily",
    "structure PaperRowsLayerEquivRibbonCollapseInput",
    "structure PaperRowsSkewProductRibbonCollapseInput",
    "PaperRowsSkewProductRibbonCollapseInput.nonemptyMainH2Input",
    "PaperRF2SkewProductInput",
    "PaperRF2LayerEquivInput",
]

H2_ROW_TOKENS = [
    "def d54PaperProductRows",
    "not_d54PaperProductRows_layerBijective",
    "not_nonempty_D54PaperProductSingletonSwitchRibbonCollapseInput",
    "D54PaperProductLayerEquivRibbonCollapseInput.nonemptyMainH2Input",
    "D54PaperProductSkewProductRibbonCollapseInput.nonemptyMainH2Input",
    "D54PaperProductSingletonSwitchRibbonCollapseInput.nonemptyMainH2Input",
    "canonicalTerminalRows_preFinalTerminalReadGoals",
    "canonicalTerminalRows_p0YShiftLastReadGoal",
    "not_preFinalP0P1RowWordReadGoals",
    "H2TableRouteSkeleton_false",
]

CHECKPOINT_TOKENS = [
    "structure FiniteBackedD7Checkpoint",
    "generatedFiniteBackedCheckpoint",
    "generatedD7M4CheckpointInput",
    "generatedD7M6CheckpointInput",
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

    checklist = (ROOT / "EvenV11/V28Hard/ChecklistFromHardParts.lean").read_text()
    if "import EvenV11.V28Hard.D7FiniteToCycleData" in checklist:
        fail("ChecklistFromHardParts imports D7FiniteToCycleData directly")
    if "import EvenV11.V28Hard.D7Checkpoint" not in checklist:
        fail("ChecklistFromHardParts does not import D7Checkpoint")
    if "paperChecklist_checkpoint_finiteBackedD7" not in checklist:
        fail("checkpoint finite-backed D7 checklist name is missing")

    h2 = (ROOT / "EvenV11/V28Hard/D5M4H2Skeleton.lean").read_text()
    for token in H2_TOKENS:
        if token not in h2:
            fail(f"H2 skeleton token missing: {token}")

    h2_rows = (ROOT / "EvenV11/V28Hard/D5M4H2PaperRows.lean").read_text()
    for token in H2_ROW_TOKENS:
        if token not in h2_rows:
            fail(f"H2 row checkpoint token missing: {token}")

    d7 = (ROOT / "EvenV11/V28Hard/D7Checkpoint.lean").read_text()
    for token in CHECKPOINT_TOKENS:
        if token not in d7:
            fail(f"D7 checkpoint token missing: {token}")

    d5_ribbon = (ROOT / "EvenV11/V28Hard/D5M4RibbonRows.lean").read_text()
    if re.search(r"structure H2Paper(Table|Certificate)Input\s*:\s*Prop", d5_ribbon):
        fail("H2 paper input wrappers should be Type-valued, not Prop-valued")

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

    print("v28 H2 skeleton static checks passed")
    print(f"required files: {len(REQUIRED)}")
    print(f"H2 route tokens: {len(H2_TOKENS)}")
    print(f"H2 row checkpoint tokens: {len(H2_ROW_TOKENS)}")
    print("D7 finite-backed use is quarantined behind D7Checkpoint")


if __name__ == "__main__":
    main()
