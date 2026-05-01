#!/usr/bin/env python3
"""Verify zero-set-only K(Z) bridge certificates.

Target B' asks for a fiber compiler that depends only on zero-set strata, or on
a finite congruence family, and whose A3 scalar monodromy invariants are units.

The post-bundle m=9 scalar certificate records a shifted zero-set mask table
``K(Z)`` plus scalar invariants, but it does not need to store the full
``kappa_perm_indices`` table.  This script expands such a mask table to the
full verifier format, checks the scalar unit condition, and optionally runs the
full finite bridge verifier.
"""

from __future__ import annotations

import argparse
import copy
import json
import math
from pathlib import Path

from verify_4plus2_allN_bridge_cert import (
    base_tuple,
    validate_certificate,
    verify_certificate,
)


def shifted_zero_mask_code(base: int, m: int) -> int:
    xs = base_tuple(base, m)
    full = (xs[0], xs[1], xs[2], xs[3], (-sum(xs)) % m)
    return sum((1 << i) for i in range(5) if full[(i + 1) % 5] == 0)


def mask_table(cert: dict) -> dict[int, int]:
    masks = cert.get("masks")
    values = cert.get("kappa_perm_indices_by_mask")
    if not isinstance(masks, list) or not isinstance(values, list):
        raise ValueError(
            "certificate must contain list fields masks and kappa_perm_indices_by_mask"
        )
    if len(masks) != len(values):
        raise ValueError("masks and kappa_perm_indices_by_mask have different lengths")
    table = {int(mask): int(value) for mask, value in zip(masks, values)}
    if len(table) != len(masks):
        raise ValueError("masks contains duplicate entries")
    return table


def expand_kappa_from_masks(cert: dict) -> list[list[int]]:
    m = cert["m"]
    table = mask_table(cert)
    kappa = []
    missing: set[int] = set()
    for _layer in range(m):
        layer = []
        for base in range(m**4):
            mask = shifted_zero_mask_code(base, m)
            value = table.get(mask)
            if value is None:
                missing.add(mask)
                value = 0
            layer.append(value)
        kappa.append(layer)
    if missing:
        raise ValueError(f"K(Z) table missing shifted zero masks: {sorted(missing)}")
    return kappa


def table_match_summary(cert: dict, expanded_kappa: list[list[int]]) -> dict:
    m = cert["m"]
    table = mask_table(cert)
    mismatches = []
    for layer, layer_table in enumerate(expanded_kappa):
        for base, actual in enumerate(layer_table):
            mask = shifted_zero_mask_code(base, m)
            expected = table[mask]
            if actual != expected:
                mismatches.append(
                    {
                        "layer": layer,
                        "base": base,
                        "mask": mask,
                        "actual": actual,
                        "expected": expected,
                    }
                )
                if len(mismatches) >= 10:
                    break
        if len(mismatches) >= 10:
            break
    return {
        "mask_shift": "mask bit i records full[(i+1) % 5] == 0",
        "mask_count": len(table),
        "table": [[mask, table[mask]] for mask in sorted(table)],
        "matches_shifted_zero_mask": not mismatches,
        "mismatch_examples": mismatches,
    }


def scalar_invariant_field(cert: dict) -> tuple[str | None, dict | None]:
    exact = f"verified_scalar_invariants_mod_{cert.get('m')}"
    if isinstance(cert.get(exact), dict):
        return exact, cert[exact]
    for key, value in cert.items():
        if key.startswith("verified_scalar_invariants_mod_") and isinstance(value, dict):
            return key, value
    return None, None


def scalar_unit_summary(cert: dict) -> dict:
    field, invariants = scalar_invariant_field(cert)
    if invariants is None:
        return {"present": False, "ok": False, "field": None}
    m = cert["m"]
    entries = {}
    failures = []
    for name, values in sorted(invariants.items()):
        if not isinstance(values, list):
            failures.append({"name": name, "reason": "not a list"})
            continue
        row = []
        for color, value in enumerate(values):
            value = int(value) % m
            unit = math.gcd(value, m) == 1
            row.append({"color": color, "value": value, "unit": unit})
            if not unit:
                failures.append({"name": name, "color": color, "value": value})
        entries[name] = row
    return {
        "present": True,
        "ok": not failures,
        "field": field,
        "modulus": m,
        "entries": entries,
        "failures": failures,
    }


def verify_zero_set_cert(path: Path, *, full_verify: bool) -> dict:
    cert = json.loads(path.read_text())
    expanded = copy.deepcopy(cert)
    expanded["kappa_perm_indices"] = expand_kappa_from_masks(cert)
    summary = {
        "path": str(path),
        "m": cert.get("m"),
        "rows": cert.get("rows"),
        "note": cert.get("note"),
        "zero_set_table": table_match_summary(cert, expanded["kappa_perm_indices"]),
        "scalar_units": scalar_unit_summary(cert),
    }
    try:
        validate_certificate(expanded)
        summary["expanded_certificate_valid"] = True
    except Exception as exc:
        summary["expanded_certificate_valid"] = False
        summary["expanded_certificate_error"] = f"{type(exc).__name__}: {exc}"
    if full_verify:
        try:
            message, _rank_summary = verify_certificate(expanded)
            summary["full_verify"] = {"ok": True, "message": message}
        except Exception as exc:
            summary["full_verify"] = {
                "ok": False,
                "error": f"{type(exc).__name__}: {exc}",
            }
    summary["ok"] = (
        summary["zero_set_table"]["matches_shifted_zero_mask"]
        and summary["scalar_units"]["ok"]
        and summary["expanded_certificate_valid"]
        and (not full_verify or summary.get("full_verify", {}).get("ok") is True)
    )
    return summary


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("cert_json", type=Path, nargs="+")
    parser.add_argument("--skip-full-verify", action="store_true")
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()

    results = [
        verify_zero_set_cert(path, full_verify=not args.skip_full_verify)
        for path in args.cert_json
    ]
    payload = {"all_ok": all(result["ok"] for result in results), "results": results}
    for result in results:
        full = result.get("full_verify", {})
        print(
            "m={m} scalar_ok={scalar_ok} table_ok={table_ok} "
            "expanded_valid={expanded_certificate_valid} full_ok={full_ok}".format(
                scalar_ok=result["scalar_units"]["ok"],
                table_ok=result["zero_set_table"]["matches_shifted_zero_mask"],
                full_ok=full.get("ok", "skipped"),
                **result,
            )
        )
    print(f"all_ok={payload['all_ok']}")
    if args.json_out:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
        print(f"wrote {args.json_out}")


if __name__ == "__main__":
    main()
