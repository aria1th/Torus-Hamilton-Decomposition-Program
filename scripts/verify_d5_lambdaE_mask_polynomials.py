#!/usr/bin/env python3
"""Verify the recorded D5 Lambda_E mask-polynomial artifact.

The artifact `certs/d5_lambdaE_mask_polynomials.json` is intended to be a
machine-readable symbolic proof object for the local parity-changing Lambda_E
layer.  This verifier recomputes the inclusion-exclusion payload from
`derive_d5_lambdaE_mask_polynomials.py`, round-trips it through JSON, and
compares it with the recorded certificate.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

import derive_d5_lambdaE_mask_polynomials as derive


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_CERT = ROOT / "certs" / "d5_lambdaE_mask_polynomials.json"


def json_normalize(payload: Any) -> Any:
    """Convert tuples and dict ordering to the same shape as JSON files."""
    return json.loads(json.dumps(payload, sort_keys=True))


def verify(cert_path: Path) -> dict[str, Any]:
    recorded = json.loads(cert_path.read_text())
    expected = json_normalize(derive.derive_payload())
    errors: list[str] = []

    if recorded != expected:
        recorded_keys = set(recorded) if isinstance(recorded, dict) else set()
        expected_keys = set(expected) if isinstance(expected, dict) else set()
        if recorded_keys != expected_keys:
            errors.append(
                "top-level key mismatch: "
                f"missing={sorted(expected_keys - recorded_keys)} "
                f"extra={sorted(recorded_keys - expected_keys)}"
            )
        for key in sorted(recorded_keys & expected_keys):
            if recorded.get(key) != expected.get(key):
                errors.append(f"mismatch at top-level key {key}")
                if len(errors) >= 8:
                    break
        if not errors:
            errors.append("payload mismatch")

    mask_entries = recorded.get("mask_entries", []) if isinstance(recorded, dict) else []
    reachable_count = sum(1 for entry in mask_entries if entry.get("reachable"))
    unreachable_count = sum(1 for entry in mask_entries if not entry.get("reachable"))
    return {
        "schema": "d5_lambdaE_mask_polynomials_verification_v1",
        "cert": str(cert_path),
        "ok": not errors,
        "errors": errors,
        "mask_entry_count": len(mask_entries),
        "reachable_mask_count": reachable_count,
        "unreachable_mask_count": unreachable_count,
        "modal_count": recorded.get("modal_count", {}).get("polynomial")
        if isinstance(recorded, dict)
        else None,
        "nonmodal_count": recorded.get("nonmodal_count", {}).get("polynomial")
        if isinstance(recorded, dict)
        else None,
        "rank_totals": {
            rank: data.get("polynomial")
            for rank, data in recorded.get("rank_totals", {}).items()
        }
        if isinstance(recorded, dict)
        else {},
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--cert", type=Path, default=DEFAULT_CERT)
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()

    summary = verify(args.cert)
    print(
        "ok",
        summary["ok"],
        "masks",
        summary["mask_entry_count"],
        "reachable",
        summary["reachable_mask_count"],
        "unreachable",
        summary["unreachable_mask_count"],
    )
    if summary["errors"]:
        for error in summary["errors"][:8]:
            print("error:", error)
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
        print(f"wrote {args.json_out}")
    if not summary["ok"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
