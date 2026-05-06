#!/usr/bin/env python3
"""Audit whether R42 evidence has reached branch-theorem status.

This is deliberately stricter than the evidence verifiers.  It distinguishes
sample-derived/supporting artifacts from the symbolic proof obligations needed
to promote residue 42 mod 48 into proof-facing Type-A coverage.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_RECORD = ROOT / "certs" / "routeE_r42_affine_branch_record.json"


def load(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text()) if path.exists() else {}


def item(name: str, ok: bool, evidence: str, level: str, missing: str | None = None) -> dict[str, Any]:
    return {
        "name": name,
        "ok": bool(ok),
        "evidence": evidence,
        "level": level,
        "missing": missing,
    }


def build_audit(record_path: Path) -> dict[str, Any]:
    record = load(record_path)
    observed = record.get("observed_law", {})
    sample = record.get("sample_verification_summary", {})
    color = record.get("color_sign_screen_summary", {})
    boundary_ver = record.get("boundary_verification_summary", {}).get("summary", {})
    boundary_expansion_ver = record.get("boundary_expansion_verification_summary", {})
    boundary_block_transducer = record.get("boundary_block_transducer_summary", {}).get(
        "summary", {}
    )
    boundary_block_transducer_ver = record.get(
        "boundary_block_transducer_verification_summary", {}
    )
    mod96_split = record.get("mod96_branch_split_summary", {})
    mod96_split_ver = record.get("mod96_branch_split_verification_summary", {})
    mod96_edges = record.get("mod96_edge_formulas_summary", {}).get("summary", {})
    mod96_edges_ver = record.get("mod96_edge_formulas_verification_summary", {})
    block_regen = record.get("block_regeneration_verification_summary", {}).get("summary", {})
    tails = record.get("open_tail_formula_suggestions_summary", {}).get("summary", {})
    time_ver = record.get("allpair_time_fit_verification_summary", {}).get("summary", {})
    transition_ver = record.get("allpair_transition_fit_verification_summary", {}).get("summary", {})
    pointwise_mining = record.get("pointwise_law_mining_summary", {}).get("summary", {})
    pointwise_mining_impact = record.get("pointwise_law_mining_summary", {}).get(
        "promotion_impact", {}
    )
    pointwise_mining_ver = record.get(
        "pointwise_law_mining_verification_summary", {}
    )
    coverage = record.get("coverage_snapshot", {})

    checklist = [
        item(
            "R42 affine family law is fixed",
            observed.get("x") == "6*q + 5"
            and observed.get("z") == "6*q + 5"
            and observed.get("symmetric") is True,
            "certs/routeE_r42_affine_branch_record.json: observed_law",
            "closed formula candidate",
        ),
        item(
            "R42 all-pair samples are reproducible",
            sample.get("all_passed") is True
            and sample.get("verified_q_values") == [0, 1, 2, 3, 4],
            "certs/routeE_r42_affine_samples_verification.json",
            "finite witness evidence",
        ),
        item(
            "R42 color-sign vector screen passes",
            color.get("all_r42_color_sign_vectors_ok") is True,
            "certs/routeE_color_sign_screen_audit.json",
            "necessary-condition screen",
        ),
        item(
            "R42 compact boundary quotient is internally verified",
            boundary_ver.get("q_ge_1_transition_fits_verified") is True
            and boundary_ver.get("q_ge_1_transition_symbolics_verified") is True
            and boundary_ver.get("q_ge_1_block_formula_symbolics_verified") is True
            and boundary_ver.get("q1_representative_block_formulas_verified") is True,
            "certs/routeE_r42_boundary_summary_verification.json",
            "supporting quotient artifact",
        ),
        item(
            "R42 boundary blocks expand to all-pair label counts",
            boundary_expansion_ver.get("schema")
            == "routeE_r42_boundary_expansion_verification_v1"
            and boundary_expansion_ver.get("ok") is True
            and boundary_expansion_ver.get("q_values") == [1, 2, 3, 4, 5, 6]
            and boundary_expansion_ver.get("block_count") == 29,
            "certs/routeE_r42_boundary_expansion_verification.json",
            "boundary-to-all-pair expansion evidence",
        ),
        item(
            "R42 block formulas match regenerated witnesses",
            block_regen.get("all_block_formulas_match_regeneration") is True
            and block_regen.get("verified_q_values") == [1, 2, 3, 4, 5, 6],
            "certs/routeE_r42_block_formula_regeneration_verification.json",
            "fresh finite regeneration evidence",
        ),
        item(
            "R42 boundary block transducer diagnostic is verified",
            boundary_block_transducer_ver.get("schema")
            == "routeE_r42_boundary_block_transducer_verification_v1"
            and boundary_block_transducer_ver.get("ok") is True
            and boundary_block_transducer_ver.get("q_values") == [1, 2, 3, 4, 5, 6]
            and boundary_block_transducer_ver.get("piecewise_fit_error_count") == 0
            and boundary_block_transducer.get("q_ge_2_support_stable") is True
            and boundary_block_transducer.get("q_ge_2_edge_count") == 69
            and boundary_block_transducer.get("edge_count_piecewise_moduli") == [2],
            "certs/routeE_r42_boundary_block_transducer.json and certs/routeE_r42_boundary_block_transducer_verification.json",
            "boundary transducer diagnostic",
        ),
        item(
            "R42 mod-96 branch split plan is verified",
            mod96_split_ver.get("schema")
            == "routeE_r42_mod96_branch_split_verification_v1"
            and mod96_split_ver.get("ok") is True
            and mod96_split_ver.get("finite_boundary_cases") == [42, 90]
            and mod96_split.get("checks", {}).get("edge_count_piecewise_moduli") == [2],
            "certs/routeE_r42_mod96_branch_split.json and certs/routeE_r42_mod96_branch_split_verification.json",
            "branch dispatcher refinement",
        ),
        item(
            "R42 mod-96 edge-count formula tables are verified",
            mod96_edges_ver.get("schema")
            == "routeE_r42_mod96_edge_formulas_verification_v1"
            and mod96_edges_ver.get("ok") is True
            and mod96_edges_ver.get("edge_count") == 69
            and mod96_edges_ver.get("error_count") == 0
            and mod96_edges.get("all_even_branch_formulas_affine_in_s") is True
            and mod96_edges.get("all_odd_branch_formulas_affine_in_s") is True,
            "certs/routeE_r42_mod96_edge_formulas.json and certs/routeE_r42_mod96_edge_formulas_verification.json",
            "branch dispatcher refinement",
        ),
        item(
            "R42 compact block open fields are only q=1 boundary exceptions",
            tails.get("suggestion_count") == 2
            and tails.get("single_sample_boundary_exception_count") == 2,
            "certs/routeE_r42_open_tail_formula_suggestions.json",
            "compression debt tracker",
        ),
        item(
            "R42 all-pair time fits verify symbolic totals",
            time_ver.get("time_total_is_m4_polynomial") is True
            and time_ver.get("label_count_fit_sum_is_node_count") is True
            and time_ver.get("dst_count_fit_sum_is_node_count") is True
            and time_ver.get("label_time_fit_sum_is_m4") is True
            and time_ver.get("dst_time_fit_sum_is_m4") is True,
            "certs/routeE_r42_allpair_time_fit_verification.json",
            "time-exhaustion evidence",
        ),
        item(
            "R42 all-pair transition matrices verify support and totals",
            transition_ver.get("transition_count_values_verified") is True
            and transition_ver.get("transition_time_values_verified") is True
            and transition_ver.get("count_row_sums_match_label_counts") is True
            and transition_ver.get("count_column_sums_match_dst_counts") is True
            and transition_ver.get("time_total_is_m4") is True
            and transition_ver.get("transition_count_support_strongly_connected") is True,
            "certs/routeE_r42_allpair_transition_fit_verification.json",
            "transition evidence",
        ),
        item(
            "R42 pointwise law-mining diagnostic is verified",
            pointwise_mining_ver.get("ok") is True
            and pointwise_mining_ver.get("q_values") == [0, 1, 2, 3, 4]
            and pointwise_mining.get("all_samples_ok") is True
            and pointwise_mining.get("all_single_cycle") is True
            and pointwise_mining.get("all_time_total_ok") is True
            and pointwise_mining.get("max_total_blocks") == 1492
            and pointwise_mining_impact.get("pointwise_equations_closed") is False
            and pointwise_mining_impact.get("no_early_closed") is False,
            "certs/routeE_r42_pointwise_law_mining.json and certs/routeE_r42_pointwise_law_mining_verification.json",
            "pointwise-law mining diagnostic",
        ),
        item(
            "R42 is still open in proof-facing coverage",
            coverage.get("r42_is_open") is True,
            "certs/routeE_typeA_residue_coverage.json",
            "coverage state",
            "Residue 42 is not yet promoted to proof-facing Type-A coverage.",
        ),
        item(
            "Pointwise first-return equations are proved for all q",
            False,
            "no artifact",
            "required theorem data",
            "Need closed formulas proving F^tau(p)=U(p) for every all-pair section point.",
        ),
        item(
            "No-early/minimality is proved for all q",
            False,
            "no artifact",
            "required theorem data",
            "Need symbolic proof that no section point returns before tau.",
        ),
        item(
            "Lean-facing endpoint theorem is present",
            False,
            "no artifact",
            "required theorem data",
            "Need theorem endpoint and name synchronized with the Route-E adapter.",
        ),
    ]
    missing_required = [
        row
        for row in checklist
        if not row["ok"] and row["level"] == "required theorem data"
    ]
    return {
        "schema": "routeE_r42_promotion_audit_v1",
        "branch": "R42",
        "record": str(record_path),
        "checklist": checklist,
        "evidence_items_ok": sum(1 for row in checklist if row["ok"]),
        "required_theorem_items_missing": missing_required,
        "promotion_ready": not missing_required and coverage.get("r42_is_open") is False,
        "conclusion": (
            "R42 has strong finite/symbolic-support evidence, but it is not "
            "promotion-ready until pointwise first-return, no-early, and "
            "Lean-facing endpoint artifacts exist."
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--record", type=Path, default=DEFAULT_RECORD)
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()

    payload = build_audit(args.record)
    print("schema", payload["schema"])
    print("promotion_ready", payload["promotion_ready"])
    print("evidence_items_ok", payload["evidence_items_ok"])
    print("required_missing", len(payload["required_theorem_items_missing"]))
    for row in payload["required_theorem_items_missing"]:
        print("missing:", row["name"])
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
        print(f"wrote {args.json_out}")


if __name__ == "__main__":
    main()
