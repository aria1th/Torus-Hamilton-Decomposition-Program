#!/usr/bin/env python3
"""Audit the corrected D5 even Route-E goal state.

This is a completion-audit helper, not a proof checker.  It maps the current
goal requirements to concrete repository artifacts and reports whether the
overall goal is actually complete.  It is intentionally conservative: open
generic branches or proof-facing-only evidence keep the goal incomplete.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]


FILES = {
    "dispatcher_doc": ROOT / "docs" / "D5_EVEN_ROUTE_E_CORRECTED_BRANCH_DISPATCHER_20260506.md",
    "audit_doc": ROOT / "docs" / "D5_EVEN_ROUTE_E_CORRECTED_BRANCH_AUDIT_20260506.md",
    "branch_summary": ROOT / "certs" / "d5_routeE_corrected_branch_summary.json",
    "typea_summary": ROOT / "certs" / "routeE_typeA_closure_package_summary.json",
    "typea_skeleton": ROOT / "certs" / "routeE_typeA_symbolic_skeleton.json",
    "typea_skeleton_verification": ROOT
    / "certs"
    / "routeE_typeA_symbolic_skeleton_verification.json",
    "coverage": ROOT / "certs" / "routeE_typeA_residue_coverage.json",
    "r38_record": ROOT / "certs" / "routeE_r38_gate_transducer_branch_record.json",
    "r38_probe": ROOT / "certs" / "routeE_r38_symmetric_probe_summary.json",
    "timeout_screen": ROOT / "certs" / "routeE_r38_m182_cpp_screen_timeout.json",
    "lambdaE_polynomials": ROOT / "certs" / "d5_lambdaE_mask_polynomials.json",
    "small_seam_family_manifest": ROOT
    / "certs"
    / "routeE_small_seam_family_scan_manifest.json",
}


def load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text()) if path.exists() else {}


def item(name: str, ok: bool, evidence: str, missing: str | None = None) -> dict:
    return {
        "name": name,
        "ok": bool(ok),
        "evidence": evidence,
        "missing": missing,
    }


def build_audit() -> dict[str, Any]:
    branch = load_json(FILES["branch_summary"])
    typea = load_json(FILES["typea_summary"])
    skeleton = load_json(FILES["typea_skeleton"])
    skeleton_verification = load_json(FILES["typea_skeleton_verification"])
    coverage = load_json(FILES["coverage"])
    r38 = load_json(FILES["r38_record"])
    probe = load_json(FILES["r38_probe"])
    timeout = load_json(FILES["timeout_screen"])
    lambdae = load_json(FILES["lambdaE_polynomials"])
    family_manifest = load_json(FILES["small_seam_family_manifest"])

    checklist = [
        item(
            "corrected branch dispatcher document exists",
            FILES["dispatcher_doc"].exists(),
            str(FILES["dispatcher_doc"]),
        ),
        item(
            "completion audit document exists",
            FILES["audit_doc"].exists(),
            str(FILES["audit_doc"]),
        ),
        item(
            "m=2 finite boundary certificate passes RF1/RF2/sign/color checks",
            branch.get("branch_E0_m2", {}).get("rf1_ok")
            and branch.get("branch_E0_m2", {}).get("rf2_ok")
            and branch.get("branch_E0_m2", {}).get("sign_ok")
            and branch.get("branch_E0_m2", {}).get("all_colors_ok"),
            "certs/d5_routeE_corrected_branch_summary.json: branch_E0_m2",
        ),
        item(
            "m=4 finite branch passes RF1/RF2/sign/color checks",
            branch.get("branch_E4_m4", {}).get("rf1_ok")
            and branch.get("branch_E4_m4", {}).get("rf2_ok")
            and branch.get("branch_E4_m4", {}).get("sign_ok")
            and branch.get("branch_E4_m4", {}).get("all_colors_ok"),
            "certs/d5_routeE_corrected_branch_summary.json: branch_E4_m4",
        ),
        item(
            "m=6..60 small-seam window has verified rank and seam evidence",
            branch.get("branch_Egen_m6_to_m60", {}).get("rank_cert_verified_all_ok")
            and branch.get("branch_Egen_m6_to_m60", {}).get("verified_all_ok"),
            "certs/d5_routeE_corrected_branch_summary.json: branch_Egen_m6_to_m60",
        ),
        item(
            "Lambda_E symbolic mask-count polynomials are recorded",
            lambdae.get("schema") == "d5_lambdaE_mask_polynomials_v1"
            and len(lambdae.get("mask_entries", [])) == 32
            and lambdae.get("modal_count", {}).get("polynomial")
            == "m^4 - 5*m^3 + 10*m^2 - 10*m + 5",
            "certs/d5_lambdaE_mask_polynomials.json",
        ),
        item(
            "B20/B16/R14e Type-A package flags are preserved and true",
            typea.get("all_recorded_flags_ok") is True,
            "certs/routeE_typeA_closure_package_summary.json",
        ),
        item(
            "B16/R14e symbolic polynomial skeleton is preserved",
            skeleton.get("schema") == "routeE_typeA_symbolic_skeleton_v1"
            and len(skeleton.get("b16", {}).get("label_sum_polynomials", {})) == 11
            and len(skeleton.get("b16", {}).get("label_dst_sum_polynomials", {})) == 29
            and len(skeleton.get("r14e", {}).get("label_sum_polynomials", [])) == 11
            and len(skeleton.get("r14e", {}).get("label_dst_sum_polynomials", [])) == 33,
            "certs/routeE_typeA_symbolic_skeleton.json",
        ),
        item(
            "B16/R14e symbolic polynomial skeleton identities verify locally",
            skeleton_verification.get("schema")
            == "routeE_typeA_symbolic_skeleton_verification_v1"
            and skeleton_verification.get("all_ok") is True,
            "certs/routeE_typeA_symbolic_skeleton_verification.json",
        ),
        item(
            "Type-A residue coverage is explicitly tracked",
            coverage.get("schema") == "routeE_typeA_residue_coverage_v1",
            "certs/routeE_typeA_residue_coverage.json",
        ),
        item(
            "Type-A residue coverage is complete",
            coverage.get("coverage_complete") is True,
            "certs/routeE_typeA_residue_coverage.json",
            "Only residues 14,16,20,40,44 mod 48 are currently proof-facing.",
        ),
        item(
            "R38 next-target record exists and is marked open",
            r38.get("schema") == "routeE_r38_gate_transducer_branch_record_v1"
            and r38.get("status") == "open_gate_transducer_target",
            "certs/routeE_r38_gate_transducer_branch_record.json",
        ),
        item(
            "R38 symmetric probe negative controls are preserved",
            probe.get("schema") == "routeE_r38_symmetric_probe_summary_v2"
            and probe.get("hits") == {"38": [5], "86": [23], "134": [5]},
            "certs/routeE_r38_symmetric_probe_summary.json",
        ),
        item(
            "timeout-safe C++ screen evidence is preserved",
            timeout.get("schema") == "d5_routeE_cpp_residue_branch_search_v1"
            and all(result.get("timeout") for result in timeout.get("results", [])),
            "certs/routeE_r38_m182_cpp_screen_timeout.json",
        ),
        item(
            "finite small-seam family scan is recorded",
            family_manifest.get("schema")
            == "d5_routeE_small_seam_family_scan_manifest_v1"
            and family_manifest.get("case_count") == 28,
            "certs/routeE_small_seam_family_scan_manifest.json",
        ),
        item(
            "E-gen-symbolic branch is closed",
            branch.get("branch_Egen_symbolic", {}).get("status") != "open",
            "certs/d5_routeE_corrected_branch_summary.json: branch_Egen_symbolic",
            "Uniform all-even full layered parity-changing template is still missing.",
        ),
    ]

    missing = [entry for entry in checklist if not entry["ok"]]
    return {
        "schema": "routeE_corrected_goal_audit_v1",
        "objective": (
            "Fill corrected d=5 even Route-E branches as far as possible and "
            "promote finite witness evidence toward symbolic proof artifacts."
        ),
        "checklist": checklist,
        "goal_complete": not missing,
        "missing_count": len(missing),
        "missing": missing,
        "conclusion": (
            "Goal is not complete: E-gen-symbolic remains open and residue "
            "coverage is incomplete."
            if missing
            else "Goal complete."
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()

    audit = build_audit()
    print("goal_complete", audit["goal_complete"])
    print("missing_count", audit["missing_count"])
    for entry in audit["missing"]:
        print("missing:", entry["name"], "-", entry.get("missing"))
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(audit, indent=2, sort_keys=True) + "\n")
        print(f"wrote {args.json_out}")


if __name__ == "__main__":
    main()
