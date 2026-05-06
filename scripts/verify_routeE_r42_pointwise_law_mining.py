#!/usr/bin/env python3
"""Verify the compact R42 pointwise-law mining artifact.

This checker does not prove the R42 branch.  It verifies that the committed
diagnostic artifact is internally consistent: sample block counts agree with
their label sums, polynomial fits reproduce the sampled values, and the artifact
still records that pointwise/no-early theorem data are not closed.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from pathlib import Path
from typing import Any

from summarize_routeE_r42_allpair_time_fits import LABELS


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_SUMMARY = ROOT / "certs" / "routeE_r42_pointwise_law_mining.json"


def coeffs(fit: dict[str, Any]) -> list[Fraction]:
    return [Fraction(text) for text in fit.get("coefficients_ascending", [])]


def eval_fit(fit: dict[str, Any], q: int) -> Fraction:
    total = Fraction(0)
    for power, coeff in enumerate(coeffs(fit)):
        total += coeff * (Fraction(q) ** power)
    return total


def fit_matches_samples(fit: dict[str, Any], points: list[tuple[int, int]]) -> bool:
    return all(eval_fit(fit, q) == value for q, value in points)


def build_verification(summary_path: Path) -> dict[str, Any]:
    payload = json.loads(summary_path.read_text())
    samples = payload.get("samples", [])
    fits = payload.get("fits", {})
    per_sample_checks = []
    for sample in samples:
        block_sum = sum(sample.get("block_counts_by_label", {}).values())
        singleton_sum = sum(sample.get("singleton_blocks_by_label", {}).values())
        rows_sum = sum(sample.get("rows_by_label", {}).values())
        per_sample_checks.append(
            {
                "q": sample.get("q"),
                "block_sum_ok": block_sum == sample.get("total_blocks"),
                "singleton_sum_ok": singleton_sum
                == sample.get("total_singleton_blocks"),
                "rows_sum_ok": rows_sum == sample.get("allpair_nodes"),
                "node_count_ok": sample.get("node_count_ok") is True,
                "time_total_ok": sample.get("time_total_ok") is True,
                "single_cycle": sample.get("single_cycle") is True,
            }
        )

    total_block_points = [
        (sample["q"], sample["total_blocks"])
        for sample in samples
        if sample.get("ok")
    ]
    singleton_points = [
        (sample["q"], sample["total_singleton_blocks"])
        for sample in samples
        if sample.get("ok")
    ]
    label_block_fit_ok = {}
    label_singleton_fit_ok = {}
    label_max_block_fit_ok = {}
    for label in LABELS:
        label_block_fit_ok[label] = fit_matches_samples(
            fits.get("block_counts_by_label", {}).get(label, {}),
            [
                (sample["q"], sample["block_counts_by_label"][label])
                for sample in samples
                if sample.get("ok")
            ],
        )
        label_singleton_fit_ok[label] = fit_matches_samples(
            fits.get("singleton_blocks_by_label", {}).get(label, {}),
            [
                (sample["q"], sample["singleton_blocks_by_label"][label])
                for sample in samples
                if sample.get("ok")
            ],
        )
        label_max_block_fit_ok[label] = fit_matches_samples(
            fits.get("max_block_length_by_label", {}).get(label, {}),
            [
                (sample["q"], sample["max_block_length_by_label"][label])
                for sample in samples
                if sample.get("ok")
            ],
        )

    ok = (
        payload.get("schema") == "routeE_r42_pointwise_law_mining_v1"
        and all(
            check["block_sum_ok"]
            and check["singleton_sum_ok"]
            and check["rows_sum_ok"]
            and check["node_count_ok"]
            and check["time_total_ok"]
            and check["single_cycle"]
            for check in per_sample_checks
        )
        and fit_matches_samples(fits.get("total_blocks", {}), total_block_points)
        and fit_matches_samples(
            fits.get("total_singleton_blocks", {}), singleton_points
        )
        and all(label_block_fit_ok.values())
        and all(label_singleton_fit_ok.values())
        and all(label_max_block_fit_ok.values())
        and payload.get("promotion_impact", {}).get("pointwise_equations_closed")
        is False
        and payload.get("promotion_impact", {}).get("no_early_closed") is False
        and payload.get("summary", {}).get("labels_without_uniform_residue_modulus")
        == ["01", "02", "03", "04", "12", "13", "14", "23", "24", "34"]
    )
    return {
        "schema": "routeE_r42_pointwise_law_mining_verification_v1",
        "summary": str(summary_path),
        "ok": ok,
        "sample_count": len(samples),
        "q_values": [sample.get("q") for sample in samples],
        "per_sample_checks": per_sample_checks,
        "fit_checks": {
            "total_blocks": fit_matches_samples(
                fits.get("total_blocks", {}), total_block_points
            ),
            "total_singleton_blocks": fit_matches_samples(
                fits.get("total_singleton_blocks", {}), singleton_points
            ),
            "block_counts_by_label": label_block_fit_ok,
            "singleton_blocks_by_label": label_singleton_fit_ok,
            "max_block_length_by_label": label_max_block_fit_ok,
        },
        "residue_affine_summary": {
            "uniform_residue_moduli_by_label": payload.get("summary", {}).get(
                "uniform_residue_moduli_by_label"
            ),
            "labels_without_uniform_residue_modulus": payload.get("summary", {}).get(
                "labels_without_uniform_residue_modulus"
            ),
        },
        "promotion_impact": payload.get("promotion_impact"),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--summary", type=Path, default=DEFAULT_SUMMARY)
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()

    verification = build_verification(args.summary)
    print("schema", verification["schema"])
    print("ok", verification["ok"])
    print("sample_count", verification["sample_count"])
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(verification, indent=2, sort_keys=True) + "\n")
        print(f"wrote {args.json_out}")
    if not verification["ok"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
