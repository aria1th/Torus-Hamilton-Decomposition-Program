#!/usr/bin/env python3
"""Verify committed D7 4+2 bridge rank fingerprints.

The compact D7 odd 4+2 witnesses are formula-defined, so the full rank arrays
need not be committed.  This script reruns the C++ compact checker through
`verify_compact_4plus2_formula_certs.py`, asks it to recompute base and fiber
rank-step fingerprints, and compares those fingerprints against the committed
manifest.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_MANIFEST = ROOT / "certs" / "d7_4plus2_rank_fingerprints.json"
DEFAULT_COMPACT_VERIFIER = ROOT / "scripts" / "verify_compact_4plus2_formula_certs.py"


def normalize_summary(summary: dict, expected: dict) -> dict:
    return {
        "name": expected["name"],
        "m": summary["m"],
        "formula": expected["formula"],
        "base_period": summary["base_period"],
        "fiber_period": summary["fiber_period"],
        "product_states": summary["product_states"],
        "colors": summary["colors"],
    }


def run_compact_verifier(
    compact_verifier: Path,
    manifest: dict,
    tmp: Path,
    *,
    target_a: bool,
    product: bool,
) -> dict:
    rank_dir = tmp / "rank_summaries"
    json_out = tmp / "compact_verify.json"
    only = ",".join(str(witness["m"]) for witness in manifest["witnesses"])
    cmd = [
        sys.executable,
        str(compact_verifier),
        "--only",
        only,
        "--rank-summary-dir",
        str(rank_dir),
        "--json-out",
        str(json_out),
    ]
    if target_a:
        cmd.append("--target-a")
    if product:
        cmd.append("--product")
    subprocess.run(cmd, cwd=ROOT, check=True)
    verify_payload = json.loads(json_out.read_text())
    generated = {}
    for result in verify_payload["results"]:
        path = Path(result["rank_summary_json"])
        summary = json.loads(path.read_text())
        generated[result["name"]] = normalize_summary(summary, result)
    return {
        "compact_verify": verify_payload,
        "generated": generated,
    }


def compare_manifest(manifest: dict, generated: dict) -> dict:
    expected_by_name = {item["name"]: item for item in manifest["witnesses"]}
    expected_names = set(expected_by_name)
    generated_names = set(generated)
    missing = sorted(expected_names - generated_names)
    extra = sorted(generated_names - expected_names)
    results = []
    for name in sorted(expected_names & generated_names):
        expected = expected_by_name[name]
        got = generated[name]
        mismatches = []
        for key in ("m", "formula", "base_period", "fiber_period", "product_states", "colors"):
            if got.get(key) != expected.get(key):
                mismatches.append(key)
        results.append(
            {
                "name": name,
                "m": expected["m"],
                "ok": not mismatches,
                "mismatches": mismatches,
                "color_count": len(expected["colors"]),
            }
        )
    return {
        "schema": manifest.get("schema"),
        "witness_count": len(results),
        "missing": missing,
        "extra": extra,
        "all_ok": all(item["ok"] for item in results) and not missing and not extra,
        "results": results,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--compact-verifier", type=Path, default=DEFAULT_COMPACT_VERIFIER)
    parser.add_argument(
        "--target-a",
        action="store_true",
        help="also rerun the Python Target-A section/column audits",
    )
    parser.add_argument(
        "--product",
        action="store_true",
        help="also rerun direct product-return checks in the C++ verifier",
    )
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()

    manifest = json.loads(args.manifest.read_text())
    with tempfile.TemporaryDirectory() as tmp_dir:
        generated_payload = run_compact_verifier(
            args.compact_verifier,
            manifest,
            Path(tmp_dir),
            target_a=args.target_a,
            product=args.product,
        )
        summary = compare_manifest(manifest, generated_payload["generated"])
        summary["manifest"] = str(args.manifest)
        summary["target_a_checked"] = args.target_a
        summary["product_checked"] = args.product

    print(
        "witnesses",
        summary["witness_count"],
        "all_ok",
        summary["all_ok"],
        "missing",
        summary["missing"],
        "extra",
        summary["extra"],
    )
    for result in summary["results"]:
        if not result["ok"]:
            print("bad", result["name"], result["mismatches"])
    if args.json_out is not None:
        args.json_out.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    if not summary["all_ok"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
