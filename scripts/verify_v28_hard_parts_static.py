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
    "EvenV11/V28Hard/TerminalA2EndpointRank.lean",
    "EvenV11/V28Hard/D3TerminalA2M4Bridge.lean",
    "EvenV11/V28Hard/D3M4DirectRootFlat.lean",
    "EvenV11/LowD5M4RibbonInterface.lean",
    "EvenV11/LowD5M4TameObstruction.lean",
    "EvenV11/V28Hard/D7TwoRailRelay.lean",
    "EvenV11/V28Hard/HighEvenEndpointPromotions.lean",
    "EvenV11/V28Hard/ChecklistFromHardParts.lean",
    "EvenV11/V28Hard/ChecklistH2RootFlat.lean",
    "docs/V28_HARD_PARTS_CODE_NOTES_20260606.md",
    "docs/V28_H2_SKELETON_PLAN_20260607.md",
]

A2_TOKENS = [
    "structure TerminalA2LowModFiniteBundle",
    "terminalA2LowModFiniteBundle",
    "abbrev TerminalA2CarrierCyclicityFamily",
    "def terminalEndpointEplus",
    "def terminalEndpointEminus",
    "boundary0_Eplus",
    "boundary1_Eminus",
    "boundary2_Eplus",
    "structure TerminalA2RootFlatRealizationAt",
    "structure TerminalA2RootFlatRealizationFamily",
    "sectionEquiv",
    "cycleData_of_finiteCyclicity_and_realizationAt",
    "cycleDataFamily_of_carrierCyclicity_and_realization",
    "terminalA2ParametricSolution_of_realization",
]

BRIDGE_TOKENS = [
    "terminalA2M4RealizationAt_of_physical",
    "terminalA2M4CycleData_of_physical",
]

D3_M4_DIRECT_TOKENS = [
    "namespace D3M4DirectRootFlat",
    "def cycleData",
    "theorem nonemptyCycleData",
]

ENDPOINT_RANK_TOKENS = [
    "namespace TerminalA2EndpointRank",
    "def endpoint0Point",
    "def endpoint1Point",
    "def endpoint2Point",
    "theorem endpointPoint_m6_injective",
    "theorem terminalEndpointA_eq_B_forces_exception",
    "theorem terminalEndpointA_injective",
    "theorem endpointDescPoint_injective_of_valid",
    "theorem endpointPoint_injective_of_desc_injective",
    "theorem endpointDesc_injective_of_even_six_le",
    "theorem endpointPoint_injective_of_even_six_le",
    "theorem endpointPoint_odd_color2_not_injective",
    "theorem endpointPoint_m7_color2_not_injective",
    "def endpointDescSucc",
    "theorem terminalCompressedEndpointReturn_endpointDescSucc",
    "theorem endpointImageSucc_singleCycle",
    "theorem compressedEndpoint_rank_step_of_desc_rank_step",
    "theorem compressedEndpointImageMap_singleCycle_of_rank_step",
    "theorem endpointImageSucc_singleCycle_of_even_six_le",
    "theorem compressedEndpointImageMap_singleCycle_of_even_six_le_rank_step",
    "theorem compressedEndpointImageMap_singleCycle_of_even_six_le_desc_rank_step",
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
    a2 = (ROOT / "EvenV11/V28Hard/D3TerminalA2Parametric.lean").read_text()
    endpoint_rank = (ROOT / "EvenV11/V28Hard/TerminalA2EndpointRank.lean").read_text()
    a2_m4 = (ROOT / "EvenV11/V28Hard/D3TerminalA2M4Bridge.lean").read_text()
    d3_m4_direct = (ROOT / "EvenV11/V28Hard/D3M4DirectRootFlat.lean").read_text()
    for token in A2_TOKENS:
        if token not in a2:
            fail(f"terminal A2 payload token missing: {token}")
    for token in BRIDGE_TOKENS:
        if token not in a2_m4:
            fail(f"terminal A2 m=4 bridge token missing: {token}")
    for token in D3_M4_DIRECT_TOKENS:
        if token not in d3_m4_direct:
            fail(f"D3 m=4 direct root-flat token missing: {token}")
    for token in ENDPOINT_RANK_TOKENS:
        if token not in endpoint_rank:
            fail(f"terminal A2 endpoint-rank token missing: {token}")

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
    print(f"terminal A2 payload tokens: {len(A2_TOKENS)}")
    print(f"terminal A2 m=4 bridge tokens: {len(BRIDGE_TOKENS)}")
    print(f"D3 m=4 direct root-flat tokens: {len(D3_M4_DIRECT_TOKENS)}")
    print(f"terminal A2 endpoint-rank tokens: {len(ENDPOINT_RANK_TOKENS)}")
    print(f"explicit sorry sites: {len(sorry_sites)}")
    for site in sorry_sites:
        print(f"  {site}")


if __name__ == "__main__":
    main()
