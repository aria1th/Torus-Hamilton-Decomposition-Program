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
    "no_go_branch_verification": ROOT
    / "certs"
    / "routeE_no_go_branch_verification.json",
    "color_sign_screen": ROOT / "certs" / "routeE_color_sign_screen_audit.json",
    "b20_branch": ROOT / "certs" / "d5_routeE_b20_branch_verify_m20_44_68.json",
    "typea_summary": ROOT / "certs" / "routeE_typeA_closure_package_summary.json",
    "typea_skeleton": ROOT / "certs" / "routeE_typeA_symbolic_skeleton.json",
    "typea_skeleton_verification": ROOT
    / "certs"
    / "routeE_typeA_symbolic_skeleton_verification.json",
    "coverage": ROOT / "certs" / "routeE_typeA_residue_coverage.json",
    "allpair_portfolio": ROOT / "certs" / "routeE_allpair_portfolio_summary.json",
    "allpair_portfolio_fits": ROOT
    / "certs"
    / "routeE_allpair_portfolio_fit_summary.json",
    "open_residue_queue": ROOT / "certs" / "routeE_open_residue_queue.json",
    "r38_record": ROOT / "certs" / "routeE_r38_gate_transducer_branch_record.json",
    "r42_record": ROOT / "certs" / "routeE_r42_affine_branch_record.json",
    "r42_sample_verification": ROOT
    / "certs"
    / "routeE_r42_affine_samples_verification.json",
    "r42_boundary_summary": ROOT
    / "certs"
    / "routeE_r42_boundary_quotient_summary.json",
    "r42_boundary_verification": ROOT
    / "certs"
    / "routeE_r42_boundary_summary_verification.json",
    "r42_boundary_expansion_verification": ROOT
    / "certs"
    / "routeE_r42_boundary_expansion_verification.json",
    "r42_block_regeneration_verification": ROOT
    / "certs"
    / "routeE_r42_block_formula_regeneration_verification.json",
    "r42_open_tail_suggestions": ROOT
    / "certs"
    / "routeE_r42_open_tail_formula_suggestions.json",
    "r42_allpair_time_fits": ROOT / "certs" / "routeE_r42_allpair_time_fit_summary.json",
    "r42_allpair_time_verification": ROOT
    / "certs"
    / "routeE_r42_allpair_time_fit_verification.json",
    "r42_allpair_transition_fits": ROOT
    / "certs"
    / "routeE_r42_allpair_transition_fit_summary.json",
    "r42_allpair_transition_verification": ROOT
    / "certs"
    / "routeE_r42_allpair_transition_fit_verification.json",
    "r42_pointwise_law_mining": ROOT / "certs" / "routeE_r42_pointwise_law_mining.json",
    "r42_pointwise_law_mining_verification": ROOT
    / "certs"
    / "routeE_r42_pointwise_law_mining_verification.json",
    "r42_promotion_audit": ROOT / "certs" / "routeE_r42_promotion_audit.json",
    "r38_probe": ROOT / "certs" / "routeE_r38_symmetric_probe_summary.json",
    "timeout_screen": ROOT / "certs" / "routeE_r38_m182_cpp_screen_timeout.json",
    "open_residue_smoke": ROOT
    / "certs"
    / "routeE_open_residue_cpp_smoke_summary_20260506.json",
    "lambdaE_polynomials": ROOT / "certs" / "d5_lambdaE_mask_polynomials.json",
    "lambdaE_verification": ROOT
    / "certs"
    / "d5_lambdaE_mask_polynomials_verification.json",
    "small_seam_family_manifest": ROOT
    / "certs"
    / "routeE_small_seam_family_scan_manifest.json",
    "small_seam_family_verification": ROOT
    / "certs"
    / "routeE_small_seam_family_scan_verification.json",
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
    no_go_branch_verification = load_json(FILES["no_go_branch_verification"])
    color_sign_screen = load_json(FILES["color_sign_screen"])
    b20 = load_json(FILES["b20_branch"])
    typea = load_json(FILES["typea_summary"])
    skeleton = load_json(FILES["typea_skeleton"])
    skeleton_verification = load_json(FILES["typea_skeleton_verification"])
    coverage = load_json(FILES["coverage"])
    portfolio = load_json(FILES["allpair_portfolio"])
    portfolio_fits = load_json(FILES["allpair_portfolio_fits"])
    open_residue_queue = load_json(FILES["open_residue_queue"])
    r38 = load_json(FILES["r38_record"])
    r42 = load_json(FILES["r42_record"])
    r42_sample_verification = load_json(FILES["r42_sample_verification"])
    r42_boundary_summary = load_json(FILES["r42_boundary_summary"])
    r42_boundary_verification = load_json(FILES["r42_boundary_verification"])
    r42_boundary_expansion_verification = load_json(
        FILES["r42_boundary_expansion_verification"]
    )
    r42_block_regeneration_verification = load_json(
        FILES["r42_block_regeneration_verification"]
    )
    r42_open_tail_suggestions = load_json(FILES["r42_open_tail_suggestions"])
    r42_allpair_time_fits = load_json(FILES["r42_allpair_time_fits"])
    r42_allpair_time_verification = load_json(FILES["r42_allpair_time_verification"])
    r42_allpair_transition_fits = load_json(FILES["r42_allpair_transition_fits"])
    r42_allpair_transition_verification = load_json(
        FILES["r42_allpair_transition_verification"]
    )
    r42_pointwise_law_mining = load_json(FILES["r42_pointwise_law_mining"])
    r42_pointwise_law_mining_verification = load_json(
        FILES["r42_pointwise_law_mining_verification"]
    )
    r42_promotion_audit = load_json(FILES["r42_promotion_audit"])
    probe = load_json(FILES["r38_probe"])
    timeout = load_json(FILES["timeout_screen"])
    open_residue_smoke = load_json(FILES["open_residue_smoke"])
    lambdae = load_json(FILES["lambdaE_polynomials"])
    lambdae_verification = load_json(FILES["lambdaE_verification"])
    family_manifest = load_json(FILES["small_seam_family_manifest"])
    family_verification = load_json(FILES["small_seam_family_verification"])

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
            "discarded X1/X2 branch mechanisms have machine-readable no-go audit",
            no_go_branch_verification.get("schema")
            == "routeE_no_go_branch_verification_v1"
            and no_go_branch_verification.get("all_ok") is True
            and no_go_branch_verification.get("X1_even_prefix_count", {}).get(
                "all_samples_contradict"
            )
            is True
            and no_go_branch_verification.get("X2_adjacent_kempe_only", {}).get(
                "all_samples_contradict"
            )
            is True,
            "certs/routeE_no_go_branch_verification.json",
        ),
        item(
            "color-by-color sign vector and repeated-block screens are recorded",
            color_sign_screen.get("schema") == "routeE_color_sign_screen_audit_v1"
            and color_sign_screen.get("all_recorded_color_sign_screens_ok") is True
            and color_sign_screen.get("explicit_all_color_sign_vectors_ok") is True
            and color_sign_screen.get("one_lambda_E_all_color_sign_vectors_ok") is True
            and color_sign_screen.get("block_power_screen", {}).get(
                "stationary_branch_discarded"
            )
            is True,
            "certs/routeE_color_sign_screen_audit.json",
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
            "Lambda_E symbolic mask-count polynomials verify by recomputation",
            lambdae_verification.get("schema")
            == "d5_lambdaE_mask_polynomials_verification_v1"
            and lambdae_verification.get("ok") is True
            and lambdae_verification.get("mask_entry_count") == 32,
            "certs/d5_lambdaE_mask_polynomials_verification.json",
        ),
        item(
            "B20 Type-A sample branch verifier is preserved and true",
            b20.get("schema") == "d5_routeE_b20_branch_v1"
            and b20.get("all_ok") is True
            and b20.get("moduli") == [20, 44, 68, 92],
            "certs/d5_routeE_b20_branch_verify_m20_44_68.json",
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
            "all-pair portfolio sample coverage is recorded separately from proofs",
            portfolio.get("schema") == "routeE_allpair_portfolio_summary_v1"
            and portfolio.get("all_even_residues_covered_by_samples") is True
            and portfolio.get("portfolio_only_count") == 19,
            "certs/routeE_allpair_portfolio_summary.json",
        ),
        item(
            "all-pair portfolio affine-fit summary identifies next symbolic candidate",
            portfolio_fits.get("schema") == "routeE_allpair_portfolio_fit_summary_v1"
            and portfolio_fits.get("portfolio_only_affine_xz_residues") == [42]
            and portfolio_fits.get("next_symbolic_candidate") == 42,
            "certs/routeE_allpair_portfolio_fit_summary.json",
        ),
        item(
            "open-residue promotion queue is recorded",
            open_residue_queue.get("schema") == "routeE_open_residue_queue_v1"
            and open_residue_queue.get("summary", {}).get("coverage_complete") is False
            and open_residue_queue.get("summary", {})
            .get("residues_by_status", {})
            .get("proof_facing")
            == [14, 16, 20, 40, 44]
            and open_residue_queue.get("summary", {})
            .get("residues_by_status", {})
            .get("active_promotion_target")
            == [42]
            and open_residue_queue.get("summary", {})
            .get("residues_by_status", {})
            .get("gate_transducer_target")
            == [38]
            and open_residue_queue.get("summary", {}).get("status_counts", {}).get(
                "portfolio_only_symmetric_nonaffine"
            )
            == 15
            and open_residue_queue.get("summary", {}).get("status_counts", {}).get(
                "portfolio_only_nonaffine"
            )
            == 2,
            "certs/routeE_open_residue_queue.json",
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
            "R42 affine next-target record exists and is marked open",
            r42.get("schema") == "routeE_r42_affine_branch_record_v1"
            and r42.get("status") == "sample_verified_open_symbolic_candidate"
            and r42.get("observed_law", {}).get("x") == "6*q + 5"
            and r42.get("coverage_snapshot", {}).get("r42_is_open") is True,
            "certs/routeE_r42_affine_branch_record.json",
        ),
        item(
            "R42 branch record indexes current verification and sign artifacts",
            r42.get("sample_moduli") == [42, 90, 138, 186, 234]
            and r42.get("boundary_verification_summary", {}).get("ok") is True
            and r42.get("boundary_summary", {})
            .get("q_ge_1_block_formula_fits_summary", {})
            .get("block24_q_ge_2_tail", {})
            .get("terminal_affine_alpha_q_ge_2")
            == "4*q + 3"
            and r42.get("boundary_summary", {})
            .get("q_ge_1_block_formula_fits_summary", {})
            .get("block24_q_ge_2_tail", {})
            .get("terminal_affine_beta_q_ge_2")
            == "12*q + 10"
            and r42.get("color_sign_screen_summary", {}).get(
                "all_r42_color_sign_vectors_ok"
            )
            is True,
            "certs/routeE_r42_affine_branch_record.json",
        ),
        item(
            "R42 pointwise law-mining diagnostic is recorded and verified",
            r42_pointwise_law_mining.get("schema")
            == "routeE_r42_pointwise_law_mining_v1"
            and r42_pointwise_law_mining.get("summary", {}).get("q_values")
            == [0, 1, 2, 3, 4]
            and r42_pointwise_law_mining.get("summary", {}).get(
                "all_samples_ok"
            )
            is True
            and r42_pointwise_law_mining.get("summary", {}).get(
                "max_total_blocks"
            )
            == 1492
            and r42_pointwise_law_mining.get("promotion_impact", {}).get(
                "pointwise_equations_closed"
            )
            is False
            and r42_pointwise_law_mining_verification.get("schema")
            == "routeE_r42_pointwise_law_mining_verification_v1"
            and r42_pointwise_law_mining_verification.get("ok") is True,
            "certs/routeE_r42_pointwise_law_mining.json and certs/routeE_r42_pointwise_law_mining_verification.json",
        ),
        item(
            "R42 affine q=0..4 samples verify with all-pair checker",
            r42_sample_verification.get("schema")
            == "routeE_r42_affine_samples_verification_v1"
            and r42_sample_verification.get("all_passed") is True
            and [
                sample.get("q")
                for sample in r42_sample_verification.get("samples", [])
            ]
            == [0, 1, 2, 3, 4],
            "certs/routeE_r42_affine_samples_verification.json",
        ),
        item(
            "R42 boundary quotient summary is compact and stable for q>=1",
            r42_boundary_summary.get("schema")
            == "routeE_r42_boundary_quotient_summary_v1"
            and r42_boundary_summary.get("raw_csv_preserved") is False
            and r42_boundary_summary.get("q_ge_1_stability", {}).get(
                "stable_block_count"
            )
            is True
            and r42_boundary_summary.get("q_ge_1_stability", {}).get(
                "stable_block_count_by_label"
            )
            is True
            and r42_boundary_summary.get("q_ge_1_stability", {}).get(
                "all_boundary_single_cycle"
            )
            is True
            and r42_boundary_summary.get("q_ge_1_transition_count_fits", {})
            .get("Z", {})
            .get("03")
            == "1"
            and r42_boundary_summary.get("q_ge_1_transition_count_fits", {})
            .get("34", {})
            .get("34")
            == "12*q + 10",
            "certs/routeE_r42_boundary_quotient_summary.json",
        ),
        item(
            "R42 representative q=1 boundary block table is preserved",
            len(r42_boundary_summary.get("representative_q1_block_table", [])) == 29,
            "certs/routeE_r42_boundary_quotient_summary.json: representative_q1_block_table",
        ),
        item(
            "R42 q>=1 run-normalized boundary block formula fits are stable",
            r42_boundary_summary.get("q_ge_1_block_formula_fits", {}).get(
                "stable_structural_keys"
            )
            is True
            and r42_boundary_summary.get("q_ge_1_block_formula_fits", {}).get(
                "block_count"
            )
            == 29
            and len(
                r42_boundary_summary.get("q_ge_1_block_formula_fits", {}).get(
                    "blocks", []
                )
            )
            == 29,
            "certs/routeE_r42_boundary_quotient_summary.json: q_ge_1_block_formula_fits",
        ),
        item(
            "R42 compact boundary summary verifies internally",
            r42_boundary_verification.get("schema")
            == "routeE_r42_boundary_summary_verification_v1"
            and r42_boundary_verification.get("ok") is True
            and r42_boundary_verification.get("summary", {}).get(
                "q_ge_1_transition_fits_verified"
            )
            is True
            and r42_boundary_verification.get("summary", {}).get(
                "q_ge_1_transition_symbolics_verified"
            )
            is True
            and r42_boundary_verification.get("summary", {}).get(
                "q_ge_1_block_formula_symbolics_verified"
            )
            is True
            and r42_boundary_verification.get("summary", {}).get(
                "q1_representative_block_formulas_verified"
            )
            is True
            and r42_boundary_verification.get("summary", {}).get(
                "stability_verified"
            )
            is True
            # The only q=1 null fields currently recorded have q>=2 tail affine
            # formulas, so future regenerations should not silently lose them.
            and r42_boundary_verification.get("summary", {}).get(
                "q1_null_fields_have_q_ge_2_tail_formulas"
            )
            is True,
            "certs/routeE_r42_boundary_summary_verification.json",
        ),
        item(
            "R42 boundary expansion matches all-pair label counts",
            r42_boundary_expansion_verification.get("schema")
            == "routeE_r42_boundary_expansion_verification_v1"
            and r42_boundary_expansion_verification.get("ok") is True
            and r42_boundary_expansion_verification.get("block_count") == 29
            and r42_boundary_expansion_verification.get("q_values")
            == [1, 2, 3, 4, 5, 6],
            "certs/routeE_r42_boundary_expansion_verification.json",
        ),
        item(
            "R42 block formulas match freshly regenerated finite witnesses",
            r42_block_regeneration_verification.get("schema")
            == "routeE_r42_block_formula_regeneration_verification_v1"
            and r42_block_regeneration_verification.get("ok") is True
            and r42_block_regeneration_verification.get("summary", {}).get(
                "verified_q_values"
            )
            == [1, 2, 3, 4, 5, 6]
            and r42_block_regeneration_verification.get("summary", {}).get(
                "all_block_formulas_match_regeneration"
            )
            is True
            and r42_block_regeneration_verification.get("summary", {}).get(
                "all_boundary_single_cycle"
            )
            is True
            and r42_block_regeneration_verification.get("summary", {}).get(
                "block_count"
            )
            == 29,
            "certs/routeE_r42_block_formula_regeneration_verification.json",
        ),
        item(
            "R42 remaining open tail fields are reduced to q=1 boundary exceptions",
            r42_open_tail_suggestions.get("schema")
            == "routeE_r42_open_tail_formula_suggestions_v1"
            and r42_open_tail_suggestions.get("summary", {}).get(
                "suggestion_count"
            )
            == 2
            and r42_open_tail_suggestions.get("summary", {}).get(
                "linear_tail_count"
            )
            == 0
            and r42_open_tail_suggestions.get("summary", {}).get(
                "single_sample_boundary_exception_count"
            )
            == 2
            and r42_open_tail_suggestions.get("summary", {}).get(
                "all_multi_sample_fields_linear"
            )
            is True,
            "certs/routeE_r42_open_tail_formula_suggestions.json",
        ),
        item(
            "R42 all-pair time polynomial fits are recorded and verified",
            r42_allpair_time_fits.get("schema")
            == "routeE_r42_allpair_time_fit_summary_v1"
            and r42_allpair_time_fits.get("summary", {}).get("all_samples_ok")
            is True
            and r42_allpair_time_fits.get("summary", {}).get("all_single_cycle")
            is True
            and r42_allpair_time_fits.get("summary", {}).get("all_time_total_ok")
            is True
            and r42_allpair_time_fits.get("summary", {}).get("time_total_degree")
            == 4
            and r42_allpair_time_verification.get("schema")
            == "routeE_r42_allpair_time_fit_verification_v1"
            and r42_allpair_time_verification.get("ok") is True
            and r42_allpair_time_verification.get("summary", {}).get(
                "time_total_is_m4_polynomial"
            )
            is True
            and r42_allpair_time_verification.get("summary", {}).get(
                "label_count_fit_sum_is_node_count"
            )
            is True
            and r42_allpair_time_verification.get("summary", {}).get(
                "dst_count_fit_sum_is_node_count"
            )
            is True
            and r42_allpair_time_verification.get("summary", {}).get(
                "label_time_fit_sum_is_m4"
            )
            is True
            and r42_allpair_time_verification.get("summary", {}).get(
                "dst_time_fit_sum_is_m4"
            )
            is True,
            "certs/routeE_r42_allpair_time_fit_summary.json and certs/routeE_r42_allpair_time_fit_verification.json",
        ),
        item(
            "R42 all-pair transition polynomial matrices are recorded and verified",
            r42_allpair_transition_fits.get("schema")
            == "routeE_r42_allpair_transition_fit_summary_v1"
            and r42_allpair_transition_fits.get("summary", {}).get("all_samples_ok")
            is True
            and r42_allpair_transition_fits.get("summary", {}).get(
                "transition_count_nonzero_edge_count"
            )
            == 28
            and r42_allpair_transition_verification.get("schema")
            == "routeE_r42_allpair_transition_fit_verification_v1"
            and r42_allpair_transition_verification.get("ok") is True
            and r42_allpair_transition_verification.get("summary", {}).get(
                "count_row_sums_match_label_counts"
            )
            is True
            and r42_allpair_transition_verification.get("summary", {}).get(
                "count_column_sums_match_dst_counts"
            )
            is True
            and r42_allpair_transition_verification.get("summary", {}).get(
                "time_total_is_m4"
            )
            is True
            and r42_allpair_transition_verification.get("summary", {}).get(
                "transition_count_support_strongly_connected"
            )
            is True,
            "certs/routeE_r42_allpair_transition_fit_summary.json and certs/routeE_r42_allpair_transition_fit_verification.json",
        ),
        item(
            "R42 promotion audit separates evidence from theorem blockers",
            r42_promotion_audit.get("schema") == "routeE_r42_promotion_audit_v1"
            and r42_promotion_audit.get("promotion_ready") is False
            and r42_promotion_audit.get("evidence_items_ok") == 18
            and len(r42_promotion_audit.get("required_theorem_items_missing", []))
            == 3,
            "certs/routeE_r42_promotion_audit.json",
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
            "open-residue C++ smoke screen is summarized",
            open_residue_smoke.get("schema")
            == "routeE_open_residue_cpp_smoke_summary_v1"
            and open_residue_smoke.get("task_count") == 57
            and open_residue_smoke.get("timeout_count") == 57,
            "certs/routeE_open_residue_cpp_smoke_summary_20260506.json",
        ),
        item(
            "finite small-seam family scan is recorded",
            family_manifest.get("schema")
            == "d5_routeE_small_seam_family_scan_manifest_v1"
            and family_manifest.get("case_count") == 28,
            "certs/routeE_small_seam_family_scan_manifest.json",
        ),
        item(
            "finite small-seam family scan verifies by recomputation",
            family_verification.get("schema")
            == "routeE_small_seam_family_scan_verification_v1"
            and family_verification.get("ok") is True
            and family_verification.get("bad_periods") == [6, 8, 12, 16, 24]
            and family_verification.get("nonrobust_affine_periods") == [48],
            "certs/routeE_small_seam_family_scan_verification.json",
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
