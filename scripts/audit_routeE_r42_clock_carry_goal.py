#!/usr/bin/env python3
"""Audit the current R42/B42 c-band clock-carry goal.

This audit is deliberately narrower than a Route-E branch closure audit.  It
answers the exploration question that motivated the current goal:

  Can the R42 branch be promoted by the tested c-band clock-carry refinement,
  or should that refinement be treated as failed?

The answer recorded here is negative for the tested refinement.  It does not
prove that every conceivable R42 transducer is impossible.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
FILES = {
    "c_skeleton": ROOT / "certs" / "routeE_r42_c_skeleton_verification.json",
    "carry_support": ROOT / "certs" / "routeE_r42_carry_support_atoms_verification.json",
    "carry_qtime": ROOT / "certs" / "routeE_r42_carry_qtime_atoms_verification.json",
    "bad_split": ROOT / "certs" / "routeE_r42_bad_intercept_carry_split_verification.json",
    "bad_split_stress": ROOT
    / "certs"
    / "routeE_r42_bad_intercept_carry_split_stress_verification.json",
    "unresolved_depth": ROOT
    / "certs"
    / "routeE_r42_unresolved_atom_feature_depth_verification.json",
    "promotion": ROOT / "certs" / "routeE_r42_promotion_audit.json",
}


def load(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text())


def item(name: str, ok: bool, evidence: str, note: str = "") -> dict[str, Any]:
    return {"name": name, "ok": ok, "evidence": evidence, "note": note}


def build_audit() -> dict[str, Any]:
    c_skeleton = load(FILES["c_skeleton"])
    carry_support = load(FILES["carry_support"])
    carry_qtime = load(FILES["carry_qtime"])
    bad_split = load(FILES["bad_split"])
    bad_split_stress = load(FILES["bad_split_stress"])
    unresolved_depth = load(FILES["unresolved_depth"])
    promotion = load(FILES["promotion"])

    checklist = [
        item(
            "R42 is reparameterized by c with m=8c+2 and x=z=c",
            c_skeleton.get("ok") is True
            and c_skeleton.get("schema") == "routeE_r42_c_skeleton_verification_v1",
            str(FILES["c_skeleton"]),
        ),
        item(
            "c-band support atoms cover the sampled qtime-missing supports",
            carry_support.get("ok") is True
            and carry_support.get("branch_atom_key_counts")
            == {"R42-even-q": 116, "R42-odd-q": 116},
            str(FILES["carry_support"]),
        ),
        item(
            "first c-band qtime model fits slopes but leaves nine intercept atoms per parity",
            carry_qtime.get("ok") is True
            and carry_qtime.get("diagnostic_result", {}).get("all_slopes_fit") is True
            and carry_qtime.get("diagnostic_result", {}).get(
                "bad_intercept_atom_counts"
            )
            == {"R42-even-q": 9, "R42-odd-q": 9},
            str(FILES["carry_qtime"]),
        ),
        item(
            "two-sample bad-intercept split suggests a small next carry alphabet",
            bad_split.get("ok") is True
            and bad_split.get("diagnostic_result", {}).get("one_feature_hits_per_branch")
            == {"R42-even-q": 8, "R42-odd-q": 8}
            and bad_split.get("diagnostic_result", {}).get("two_feature_hits_per_branch")
            == {"R42-even-q": 1, "R42-odd-q": 1},
            str(FILES["bad_split"]),
            "This is treated as provisional evidence only.",
        ),
        item(
            "larger stress test refutes the simple one/two-feature split",
            bad_split_stress.get("ok") is True
            and bad_split_stress.get("diagnostic_result", {}).get(
                "simple_one_or_two_feature_schema_stable"
            )
            is False
            and bad_split_stress.get("diagnostic_result", {}).get("unresolved_atom")
            == "20->26|L1|B7:7|R0:0",
            str(FILES["bad_split_stress"]),
        ),
        item(
            "unresolved atom is not uniformly rescued by tested depth-three features",
            unresolved_depth.get("ok") is True
            and unresolved_depth.get("diagnostic_result", {}).get("even_minimal_depth")
            == 3
            and unresolved_depth.get("diagnostic_result", {}).get("odd_minimal_depth")
            is None,
            str(FILES["unresolved_depth"]),
        ),
        item(
            "R42 remains non-promoted as a Route-E theorem",
            promotion.get("schema") == "routeE_r42_promotion_audit_v1"
            and promotion.get("promotion_ready") is False
            and promotion.get("evidence_items_ok") == 26,
            str(FILES["promotion"]),
        ),
    ]
    tested_refinement_failed = all(entry["ok"] for entry in checklist)
    return {
        "schema": "routeE_r42_clock_carry_goal_audit_v1",
        "objective": (
            "Explain or refute B42/R42 using the c-band clock-carry "
            "transducer program."
        ),
        "scope": {
            "refuted": "tested c-band threshold/residue carry promotion",
            "not_refuted": "all conceivable full layered R42 transducers",
            "not_proved": "R42 Route-E theorem",
        },
        "tested_refinement_failed": tested_refinement_failed,
        "r42_branch_closed": False,
        "checklist": checklist,
        "missing_for_branch_closure": [
            "closed pointwise first-return equations",
            "symbolic no-early/minimality proof",
            "Lean-facing endpoint theorem",
        ],
        "recommendation": (
            "Do not continue blind threshold/residue atom splitting.  Either "
            "introduce a genuinely new state variable from the raw zero-clock "
            "winner/carry dynamics, or demote R42 from promotion target."
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--json-out",
        type=Path,
        default=ROOT / "certs" / "routeE_r42_clock_carry_goal_audit.json",
    )
    args = parser.parse_args()
    payload = build_audit()
    print("schema", payload["schema"])
    print("tested_refinement_failed", payload["tested_refinement_failed"])
    print("r42_branch_closed", payload["r42_branch_closed"])
    print("recommendation", payload["recommendation"])
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
        print(f"wrote {args.json_out}")
    if not payload["tested_refinement_failed"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
