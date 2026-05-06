#!/usr/bin/env python3
"""Verify the D5 Route-E small-seam family scan artifacts.

This recomputes the finite affine-family scan from
`verify_d5_even_routeE.SMALL_SEAM_CASES`, then compares both the full raw scan
JSON and the compact manifest committed under `certs/`.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

import analyze_d5_routeE_small_seam_families as scan


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_RAW = ROOT / "certs" / "routeE_small_seam_family_scan_6_60.json"
DEFAULT_MANIFEST = ROOT / "certs" / "routeE_small_seam_family_scan_manifest.json"


def json_normalize(payload: Any) -> Any:
    return json.loads(json.dumps(payload, sort_keys=True))


def periods_from_payload(raw: dict[str, Any], manifest: dict[str, Any]) -> list[int]:
    if "periods" in manifest:
        return [int(x) for x in manifest["periods"]]
    return [int(item["period"]) for item in raw.get("results", [])]


def recompute(periods: list[int], normalized_slot_zero: bool) -> dict[str, Any]:
    rows = scan.case_rows(normalized=normalized_slot_zero)
    return {
        "source": "verify_d5_even_routeE.SMALL_SEAM_CASES",
        "normalized_slot_zero": normalized_slot_zero,
        "case_count": len(rows),
        "moduli": [row["m"] for row in rows],
        "results": [scan.analyze_period(period, rows) for period in periods],
    }


def mismatch_keys(expected: dict[str, Any], actual: dict[str, Any]) -> list[str]:
    keys = sorted(set(expected) | set(actual))
    return [key for key in keys if expected.get(key) != actual.get(key)]


def verify(raw_path: Path, manifest_path: Path) -> dict[str, Any]:
    raw = json.loads(raw_path.read_text())
    manifest = json.loads(manifest_path.read_text())
    periods = periods_from_payload(raw, manifest)
    expected_raw = json_normalize(
        recompute(periods, bool(raw.get("normalized_slot_zero", True)))
    )
    recorded_raw = json_normalize(raw)
    expected_manifest = json_normalize(scan.compact_manifest(expected_raw))
    recorded_manifest = json_normalize(manifest)

    raw_match = recorded_raw == expected_raw
    manifest_match = recorded_manifest == expected_manifest
    raw_mismatches = [] if raw_match else mismatch_keys(expected_raw, recorded_raw)
    manifest_mismatches = (
        [] if manifest_match else mismatch_keys(expected_manifest, recorded_manifest)
    )

    return {
        "schema": "routeE_small_seam_family_scan_verification_v1",
        "raw": str(raw_path),
        "manifest": str(manifest_path),
        "ok": raw_match and manifest_match,
        "raw_match": raw_match,
        "manifest_match": manifest_match,
        "raw_mismatches": raw_mismatches,
        "manifest_mismatches": manifest_mismatches,
        "periods": periods,
        "case_count": expected_raw.get("case_count"),
        "bad_periods": expected_manifest.get("bad_periods"),
        "nonrobust_affine_periods": expected_manifest.get(
            "nonrobust_affine_periods"
        ),
        "robust_affine_periods": expected_manifest.get("robust_affine_periods"),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--raw", type=Path, default=DEFAULT_RAW)
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()

    summary = verify(args.raw, args.manifest)
    print(
        "ok",
        summary["ok"],
        "periods",
        summary["periods"],
        "bad",
        summary["bad_periods"],
        "nonrobust",
        summary["nonrobust_affine_periods"],
    )
    if summary["raw_mismatches"]:
        print("raw_mismatches", summary["raw_mismatches"][:8])
    if summary["manifest_mismatches"]:
        print("manifest_mismatches", summary["manifest_mismatches"][:8])
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
        print(f"wrote {args.json_out}")
    if not summary["ok"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
