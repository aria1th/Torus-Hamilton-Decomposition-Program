#!/usr/bin/env python3
"""Summarize the corrected D5 even Route-E branch status.

This script is intentionally compact.  It does not search.  It gathers the
current proof-facing artifacts after the sign audit:

* the full-layered `m=2` boundary certificate;
* the embedded `m=4` finite schedule;
* the recorded non-open small-seam cases for `m=6..60`;
* the symbolic Lambda_E mask-count derivation hook;
* the proof-facing Type-A B20/B16/R14e evidence summaries;
* the removed even prefix-count branch;
* the removed adjacent-Kempe branch.

The output is a branch table suitable for copying into progress notes.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

import d5_routeE_nested_diagnostics as nested
import export_d5_even_routeE_layers as exporter
import verify_d5_even_routeE as routee
import verify_d5_routeE_small_seam_rank_certs as rank_certs


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_M2 = ROOT / "certs" / "d5_routeE_m2_full_layered_boundary.json"
DEFAULT_RANK_CERTS = ROOT / "certs" / "d5_routeE_small_seam_rank_certs.json"
DEFAULT_B20_CERT = ROOT / "certs" / "d5_routeE_b20_branch_verify_m20_44_68.json"
DEFAULT_TYPEA_CERT = ROOT / "certs" / "routeE_typeA_closure_package_summary.json"


def summarize_layers_payload(payload: dict[str, Any], colors: list[int] | None = None) -> dict:
    m = int(payload["m"])
    layers = payload["layers"]
    rf1_errors = nested.check_rf1(m, layers)
    rf2_errors, sign_product = nested.check_rf2(m, layers)
    sign_target = -1 if (5 * (m**4 - 1)) % 2 else 1
    if colors is None:
        colors = list(range(5))

    color_summaries = []
    for color in colors:
        perm = nested.return_map(m, layers, color)
        is_perm = sorted(perm) == list(range(m**4))
        cycles = nested.permutation_cycles(perm) if is_perm else []
        level_cycles = []
        level_time_ok = []
        level_perm_ok = []
        if is_perm:
            for fr in nested.nested_diagnostics(m, perm):
                level_cycles.append(fr.cycles)
                level_time_ok.append(fr.ok_time_sum)
                level_perm_ok.append(fr.ok_permutation)
        color_summaries.append(
            {
                "color": color,
                "return_perm": is_perm,
                "return_cycles": cycles,
                "level_cycles": level_cycles,
                "level_time_ok": level_time_ok,
                "level_perm_ok": level_perm_ok,
                "ok": (
                    is_perm
                    and cycles == [m**4]
                    and all(level_time_ok)
                    and all(level_perm_ok)
                    and all(c == [m ** (4 - i)] for i, c in enumerate(level_cycles, start=1))
                ),
            }
        )

    return {
        "m": m,
        "rf1_ok": not rf1_errors,
        "rf2_ok": not rf2_errors,
        "sign_product": sign_product,
        "sign_target": sign_target,
        "sign_ok": sign_product == sign_target,
        "colors": color_summaries,
        "all_colors_ok": all(c["ok"] for c in color_summaries),
    }


def summarize_m2(path: Path) -> dict:
    return summarize_layers_payload(json.loads(path.read_text()))


def summarize_m4() -> dict:
    return summarize_layers_payload(exporter.export_layers(4))


def summarize_small_seam(rank_cert_path: Path, verify: bool, verify_rank: bool) -> dict:
    cases = routee.SMALL_SEAM_CASES
    moduli = sorted(cases)
    out = {
        "case_count": len(cases),
        "moduli": moduli,
        "min_m": moduli[0] if moduli else None,
        "max_m": moduli[-1] if moduli else None,
        "rank_cert_loaded": False,
        "rank_cert_case_count": None,
        "rank_cert_moduli_match": None,
        "rank_cert_verified_all_ok": None,
        "verified_all_ok": None,
    }
    if rank_cert_path.exists():
        cert = json.loads(rank_cert_path.read_text())
        cert_moduli = [int(item["m"]) for item in cert.get("cases", [])]
        out.update(
            {
                "rank_cert_loaded": True,
                "rank_cert_case_count": cert.get("case_count"),
                "rank_cert_moduli_match": cert_moduli == moduli,
            }
        )
        if verify_rank:
            rank_summary = rank_certs.verify_cert(cert)
            out["rank_cert_verified_all_ok"] = bool(rank_summary["all_ok"])
    if verify:
        results = routee.verify_small_seam_cases(moduli)
        out["verified_all_ok"] = all(item.get("ok") for item in results)
    return out


def summarize_b20(path: Path) -> dict:
    out = {
        "cert_loaded": False,
        "schema": None,
        "moduli": [],
        "all_ok": None,
        "covers_symbolic_branch": False,
        "open_fields": [
            "ThetaPointwiseTraceTarget.firstReturn_equation",
            "ThetaPointwiseTraceTarget.firstReturn_minimal",
        ],
    }
    if path.exists():
        payload = json.loads(path.read_text())
        out.update(
            {
                "cert_loaded": True,
                "schema": payload.get("schema"),
                "moduli": payload.get("moduli", []),
                "all_ok": payload.get("all_ok"),
                "sample_checks": [
                    {
                        "m": item["m"],
                        "blocks_ok": item["translation_blocks_ok"],
                        "time_distribution_ok": item["time_distribution_ok"],
                        "return_time_formula_ok": item["return_time_formula_ok"],
                        "sum_ok": item["return_time_sum_ok"],
                    }
                    for item in payload.get("results", [])
                ],
            }
        )
    return out


def summarize_typea(path: Path) -> dict:
    out = {
        "cert_loaded": False,
        "schema": None,
        "all_recorded_flags_ok": None,
        "b16_moduli": [],
        "b16_macro_all_ok": None,
        "r14e_moduli": [],
        "r14e_insertion_comparisons_all_ok": None,
        "note": (
            "B16/R14e package summary records external verifier outputs; "
            "it is proof-facing evidence, not a closed Lean theorem."
        ),
    }
    if path.exists():
        payload = json.loads(path.read_text())
        b16 = payload.get("b16", {})
        r14e = payload.get("r14e", {})
        out.update(
            {
                "cert_loaded": True,
                "schema": payload.get("schema"),
                "all_recorded_flags_ok": payload.get("all_recorded_flags_ok"),
                "b16_moduli": b16.get("moduli", []),
                "b16_macro_all_ok": b16.get("macro_all_ok"),
                "r14e_moduli": r14e.get("moduli", []),
                "r14e_insertion_comparisons_all_ok": r14e.get(
                    "insertion_comparisons_all_ok"
                ),
            }
        )
    return out


def build_summary(args: argparse.Namespace) -> dict:
    m2 = summarize_m2(args.m2_cert)
    m4 = summarize_m4()
    small = summarize_small_seam(
        args.rank_certs, args.verify_small_seam, args.verify_rank_certs
    )
    b20 = summarize_b20(args.b20_cert)
    typea = summarize_typea(args.typea_cert)
    return {
        "schema": "d5_routeE_corrected_branch_summary_v1",
        "branch_O_odd": {
            "status": "external_existing_odd_branch",
            "note": "Use existing odd-modulus D5 input / odd machinery.",
        },
        "branch_E0_m2": {
            "status": "filled_boundary_certificate",
            **m2,
        },
        "branch_E4_m4": {
            "status": "filled_finite_C_E_O_schedule",
            **m4,
        },
        "branch_Egen_m6_to_m60": {
            "status": "finite_small_seam_evidence_window",
            **small,
            "symbolic_status": (
                "Lambda_E local mask counts are symbolic; full all-even "
                "counts/splice law is still open."
            ),
        },
        "branch_Egen_symbolic": {
            "status": "open",
            "b20": b20,
            "typeA_closure_packages": typea,
            "needed": [
                "full layered parity-changing one-layer coloring template",
                "RF1/RF2 closed verification",
                "product_t Lambda_t = -1 sign proof",
                "uniform count/slot/splice law beyond finite window",
                "no-early/minimality proof",
                "time exhaustion identity",
            ],
        },
        "branch_X1_even_prefix_count": {
            "status": "removed_by_column_parity_obstruction",
            "reason": (
                "Even m has only odd units.  Five primitive prefix-count rows "
                "would force five odd N_0 entries, so the stop-0 column sum "
                "would be odd, contradicting the local-Latin column sum m."
            ),
        },
        "branch_X2_adjacent_kempe_only": {
            "status": "removed_by_sign_obstruction",
            "reason": (
                "RF2-preserving adjacent-rank Kempe repairs preserve layer sign "
                "from cyclic bulk, but even D5 needs product_t Lambda_t = -1."
            ),
        },
    }


def markdown(summary: dict) -> str:
    e0 = summary["branch_E0_m2"]
    e4 = summary["branch_E4_m4"]
    eg = summary["branch_Egen_m6_to_m60"]
    b20 = summary["branch_Egen_symbolic"]["b20"]
    typea = summary["branch_Egen_symbolic"]["typeA_closure_packages"]
    rows = [
        ("O", "odd m", summary["branch_O_odd"]["status"], "existing odd branch"),
        (
            "X1",
            "even prefix-count",
            summary["branch_X1_even_prefix_count"]["status"],
            "discarded branch",
        ),
        (
            "X2",
            "adjacent-Kempe only",
            summary["branch_X2_adjacent_kempe_only"]["status"],
            "discarded branch",
        ),
        (
            "E0",
            "m=2",
            e0["status"],
            f"RF1={e0['rf1_ok']} RF2={e0['rf2_ok']} sign={e0['sign_ok']} colors={e0['all_colors_ok']}",
        ),
        (
            "E-small",
            "m=4",
            e4["status"],
            f"RF1={e4['rf1_ok']} RF2={e4['rf2_ok']} sign={e4['sign_ok']} colors={e4['all_colors_ok']}",
        ),
        (
            "E-gen-window",
            f"{eg['min_m']}..{eg['max_m']} even",
            eg["status"],
            (
                f"cases={eg['case_count']} rank_cert={eg['rank_cert_loaded']} "
                f"moduli_match={eg['rank_cert_moduli_match']} "
                f"rank_verified={eg['rank_cert_verified_all_ok']} "
                f"seam_verified={eg['verified_all_ok']}"
            ),
        ),
        (
            "E-gen-symbolic",
            "all large even m",
            summary["branch_Egen_symbolic"]["status"],
            (
                f"B20 samples={b20['moduli']} ok={b20['all_ok']}; "
                f"TypeA B16={typea['b16_moduli']} R14e={typea['r14e_moduli']} "
                f"ok={typea['all_recorded_flags_ok']}; uniform template still needed"
            ),
        ),
    ]
    lines = [
        "# D5 Corrected Route-E Branch Summary",
        "",
        "| branch | range | status | check |",
        "| --- | --- | --- | --- |",
    ]
    for row in rows:
        lines.append("| " + " | ".join(str(x) for x in row) + " |")
    lines.extend(
        [
            "",
            "Open symbolic gap:",
            "",
            "- The `m=2` and `m=4` branches are finite certificates.",
            "- The `m=6..60` window is verified small-seam evidence, not an all-even theorem.",
            "- The Lambda_E local defect-layer counts are symbolic by inclusion-exclusion.",
            "- The missing proof is a uniform all-even count/slot/splice law for the parity-changing full layered branch.",
        ]
    )
    return "\n".join(lines) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--m2-cert", type=Path, default=DEFAULT_M2)
    parser.add_argument("--rank-certs", type=Path, default=DEFAULT_RANK_CERTS)
    parser.add_argument("--b20-cert", type=Path, default=DEFAULT_B20_CERT)
    parser.add_argument("--typea-cert", type=Path, default=DEFAULT_TYPEA_CERT)
    parser.add_argument("--verify-small-seam", action="store_true")
    parser.add_argument("--verify-rank-certs", action="store_true")
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()

    summary = build_summary(args)
    if args.json_out is not None:
        args.json_out.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    print(markdown(summary))


if __name__ == "__main__":
    main()
