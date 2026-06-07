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
    "EvenV11/D54ReturnCore.lean",
    "EvenV11/LowD5M4TameObstruction.lean",
    "EvenV11/V28Hard/ChecklistH2RootFlat.lean",
    "EvenV11/V28Hard/ChecklistFromHardParts.lean",
    "docs/V28_H2_SKELETON_PLAN_20260607.md",
    "scripts/search_h2_terminal_transported.py",
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

H2_CORE_TOKENS = [
    "postBaseCarry_after_RbaseNeutral_eq_Rhat",
    "seedLayerReturn_twoStageFullReturnLayer",
    "physicalRowsOfSeedRow_layerMap_conj",
    "physical_layerBijective_of_seedLayer_conj",
    "structure D54ProductBaseLayerConjRealization",
    "structure D54ProductBaseSeedRowRealization",
    "structure D54TwoStageLayerConjRealization",
    "structure D54TwoStageSeedRowRealization",
    "structure D54TwoStageLayerConjSingletonSwitchRealization",
    "structure D54TwoStageSeedRowSingletonSwitchRealization",
    "finalLowD5M4RootFlatCertificateFamily_of_paperStagesTwoStageLayerConjSingleton",
    "finalLowD5M4RootFlatCertificateFamily_of_paperLayerConjStages",
    "finalLowD5M4RootFlatCertificateFamily_of_paperSeedRowStages",
    "structure TerminalA2M4SeedRowRealization",
    "finalLowD5M4RootFlatCertificateFamily_of_paperAllSeedRowStages",
    "structure TerminalA2M4TransportedSeedRowRealization",
    "terminalF0F1_iterate_7",
    "terminalF1F2_iterate_8",
    "TerminalA2M4PhysicalRealization.actualF0F1_iterate_7",
    "TerminalA2M4PhysicalRealization.actualF1F2_iterate_8",
    "TerminalA2M4PhysicalRealization.eT_ext_of_color0_return_eq",
    "TerminalA2M4TransportedSeedRowRealization.actualF0F1_iterate_7",
    "TerminalA2M4TransportedSeedRowRealization.actualF1F2_iterate_8",
    "TerminalA2M4TransportedSeedRowRealization.eT_color0_forced_orbit",
    "terminalF0F1_cycleBlockLengths",
    "terminalF0F2_cycleBlockLengths",
    "terminalF1F2_cycleBlockLengths",
    "structure D54ProductBaseTransportedSeedRowRealization",
    "structure D54TwoStageTransportedSeedRowSingletonSwitchRealization",
    "finalLowD5M4RootFlatCertificateFamily_of_paperTransportedSeedRowStages",
]

OBSTRUCTION_TOKENS = [
    "tameSeedRootEquiv",
    "no_four_rootSteps_to_tamePaperReturn_color0",
    "not_returnMapConj_tameSeedRootEquiv",
]

BROAD_ROW_READ_BLOCKER_TOKENS = [
    "not_preFinalP0P1RowWordReadGoals",
    "H2TableRouteSkeleton_false",
]

DOC_ROW_READ_BLOCKER_TOKENS = [
    "not_preFinalP0P1RowWordReadGoals",
    "H2TableRouteSkeleton_false",
    "H2SkewProductPathRouteSkeleton",
    "H2RibbonCollapseInput",
]

TERMINAL_SEARCH_TOKENS = [
    "TerminalA2M4TransportedSeedRowRealization",
    "target_triple_for_emap",
    "factor_fixed_emap",
    "relation_signature",
    "common_conjugacy",
    "f0_forced_common_conjugacy",
    "sample_four_layer_candidates",
    "two_layer_products",
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

    h2_core = (ROOT / "EvenV11/D54ReturnCore.lean").read_text()
    for token in H2_CORE_TOKENS:
        if token not in h2_core:
            fail(f"active H2 core token missing: {token}")

    terminal_search = (ROOT / "scripts/search_h2_terminal_transported.py").read_text()
    for token in TERMINAL_SEARCH_TOKENS:
        if token not in terminal_search:
            fail(f"H2 terminal search token missing: {token}")

    obstruction = (ROOT / "EvenV11/LowD5M4TameObstruction.lean").read_text()
    for token in OBSTRUCTION_TOKENS:
        if token not in obstruction:
            fail(f"H2 tame obstruction token missing: {token}")

    archived_paper_rows = (
        ROOT / "archive/EvenV11/V28Hard/D5M4H2PaperRows.lean"
    ).read_text()
    for token in BROAD_ROW_READ_BLOCKER_TOKENS:
        if token not in archived_paper_rows:
            fail(f"H2 broad row-read blocker token missing: {token}")

    h2_plan = (ROOT / "docs/V28_H2_SKELETON_PLAN_20260607.md").read_text()
    for token in DOC_ROW_READ_BLOCKER_TOKENS:
        if token not in h2_plan:
            fail(f"H2 plan no longer records broad row-read blocker: {token}")

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
    print(f"active H2 core tokens: {len(H2_CORE_TOKENS)}")
    print(f"tame obstruction tokens: {len(OBSTRUCTION_TOKENS)}")
    print(f"broad row-read blocker tokens: {len(BROAD_ROW_READ_BLOCKER_TOKENS)}")
    print("archive-dependent H2/D7 checkpoint files are quarantined under archive/")


if __name__ == "__main__":
    main()
