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
    BridgeModel,
    base_tuple,
    fiber_index,
    fiber_tuple,
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


def clock_pair_from_fiber(fiber: int, m: int) -> tuple[int, int]:
    y0, y1 = fiber_tuple(fiber, m)
    return ((y0 + y1) % m, y0)


def fiber_from_clock_pair(pair: tuple[int, int], m: int) -> int:
    s, x = pair
    return fiber_index((x % m, (s - x) % m), m)


def triangular_pair_step(
    pair: tuple[int, int], A: int, phi: list[int], m: int
) -> tuple[int, int]:
    s, x = pair
    return ((s + A) % m, (x + phi[s]) % m)


def triangular_obligation_summary(cert: dict, expanded_kappa: list[list[int]]) -> dict:
    field, invariants = scalar_invariant_field(cert)
    if invariants is None:
        return {
            "present": False,
            "ok": False,
            "field": None,
            "reason": "no verified_scalar_invariants_mod_* field",
        }
    m = cert["m"]
    A_values = invariants.get("A")
    E_values = invariants.get("E")
    rows = cert.get("rows")
    if (
        not isinstance(A_values, list)
        or not isinstance(E_values, list)
        or not isinstance(rows, list)
        or len(A_values) != len(rows)
        or len(E_values) != len(rows)
    ):
        return {
            "present": True,
            "ok": False,
            "field": field,
            "reason": "scalar invariant field must contain A/E lists matching rows",
        }

    model = BridgeModel(m)
    base_period = m**4
    colors = []
    all_errors: list[dict] = []
    for color, row in enumerate(rows):
        A = int(A_values[color]) % m
        E = int(E_values[color]) % m
        phi: list[int | None] = [None] * m
        errors: list[dict] = []
        for s in range(m):
            for x in range(m):
                start_fiber = fiber_from_clock_pair((s, x), m)
                actual_fiber = model.section_return_step(
                    start_fiber, row, expanded_kappa, 0, base_period
                )
                actual_pair = clock_pair_from_fiber(actual_fiber, m)
                expected_clock = (s + A) % m
                if actual_pair[0] != expected_clock:
                    errors.append(
                        {
                            "kind": "clock_step",
                            "s": s,
                            "x": x,
                            "actual": list(actual_pair),
                            "expected_clock": expected_clock,
                        }
                    )
                    break
                delta = (actual_pair[1] - x) % m
                if phi[s] is None:
                    phi[s] = delta
                elif phi[s] != delta:
                    errors.append(
                        {
                            "kind": "phi_depends_on_x",
                            "s": s,
                            "x": x,
                            "actual_delta": delta,
                            "expected_delta": phi[s],
                            "actual": list(actual_pair),
                        }
                    )
                    break
            if errors:
                break

        phi_values = [int(value) if value is not None else None for value in phi]
        if not errors and all(value is not None for value in phi_values):
            phi_int = [int(value) for value in phi_values]
            for s in range(m):
                for x in range(m):
                    start_fiber = fiber_from_clock_pair((s, x), m)
                    actual_pair = clock_pair_from_fiber(
                        model.section_return_step(
                            start_fiber, row, expanded_kappa, 0, base_period
                        ),
                        m,
                    )
                    expected_pair = triangular_pair_step((s, x), A, phi_int, m)
                    if actual_pair != expected_pair:
                        errors.append(
                            {
                                "kind": "section_triangular_mismatch",
                                "s": s,
                                "x": x,
                                "actual": list(actual_pair),
                                "expected": list(expected_pair),
                            }
                        )
                        break
                if errors:
                    break
            for x in range(m):
                pair = (0, x)
                for _step in range(m):
                    pair = triangular_pair_step(pair, A, phi_int, m)
                expected_pair = (0, (x + E) % m)
                if pair != expected_pair:
                    errors.append(
                        {
                            "kind": "round_at_zero",
                            "x": x,
                            "actual": list(pair),
                            "expected": list(expected_pair),
                        }
                    )
                    break

        A_unit = math.gcd(A, m) == 1
        E_unit = math.gcd(E, m) == 1
        if not A_unit:
            errors.append({"kind": "A_not_unit", "A": A})
        if not E_unit:
            errors.append({"kind": "E_not_unit", "E": E})
        color_summary = {
            "color": color,
            "A": A,
            "E": E,
            "A_unit": A_unit,
            "E_unit": E_unit,
            "phi": phi_values,
            "section_matches_triangular": not any(
                error["kind"]
                in {"clock_step", "phi_depends_on_x", "section_triangular_mismatch"}
                for error in errors
            ),
            "round_at_zero_ok": not any(
                error["kind"] == "round_at_zero" for error in errors
            ),
            "ok": not errors,
            "errors": errors[:10],
        }
        colors.append(color_summary)
        all_errors.extend({"color": color, **error} for error in errors)

    return {
        "present": True,
        "ok": not all_errors,
        "field": field,
        "modulus": m,
        "base_period": base_period,
        "lean_certificate": "A3TriangularScalarCertificate",
        "clock_pair": "(s, x) = (y0 + y1, y0)",
        "colors": colors,
        "failures": all_errors[:20],
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
        "triangular_obligations": triangular_obligation_summary(
            cert, expanded["kappa_perm_indices"]
        ),
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
        and summary["triangular_obligations"]["ok"]
        and summary["expanded_certificate_valid"]
        and (not full_verify or summary.get("full_verify", {}).get("ok") is True)
    )
    return summary


def compact_triangular_manifest(result: dict) -> dict:
    triangular = result["triangular_obligations"]
    return {
        "schema": "d7_targetB_triangular_obligations_v1",
        "m": result["m"],
        "base_period": triangular["base_period"],
        "lean_certificate": triangular["lean_certificate"],
        "clock_pair": triangular["clock_pair"],
        "colors": [
            {
                "color": color["color"],
                "A": color["A"],
                "E": color["E"],
                "A_unit": color["A_unit"],
                "E_unit": color["E_unit"],
                "phi": color["phi"],
                "section_matches_triangular": color["section_matches_triangular"],
                "round_at_zero_ok": color["round_at_zero_ok"],
            }
            for color in triangular["colors"]
        ],
    }


def compare_triangular_manifest(expected: dict, actual: dict) -> dict:
    keys = ("schema", "m", "base_period", "lean_certificate", "clock_pair", "colors")
    mismatches = [key for key in keys if expected.get(key) != actual.get(key)]
    return {
        "ok": not mismatches,
        "mismatches": mismatches,
        "expected_color_count": len(expected.get("colors", [])),
        "actual_color_count": len(actual.get("colors", [])),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("cert_json", type=Path, nargs="+")
    parser.add_argument("--skip-full-verify", action="store_true")
    parser.add_argument("--json-out", type=Path)
    parser.add_argument(
        "--write-triangular-manifest",
        type=Path,
        help="write compact A/E/phi/roundAtZero manifest for one certificate",
    )
    parser.add_argument(
        "--triangular-manifest",
        type=Path,
        help="compare one certificate against a committed triangular manifest",
    )
    args = parser.parse_args()

    results = [
        verify_zero_set_cert(path, full_verify=not args.skip_full_verify)
        for path in args.cert_json
    ]
    payload = {"results": results}
    triangular_manifest_check = None
    if args.write_triangular_manifest is not None:
        if len(results) != 1:
            raise SystemExit("--write-triangular-manifest requires exactly one certificate")
        manifest = compact_triangular_manifest(results[0])
        args.write_triangular_manifest.parent.mkdir(parents=True, exist_ok=True)
        args.write_triangular_manifest.write_text(
            json.dumps(manifest, indent=2, sort_keys=True) + "\n"
        )
        print(f"wrote {args.write_triangular_manifest}")
    if args.triangular_manifest is not None:
        if len(results) != 1:
            raise SystemExit("--triangular-manifest requires exactly one certificate")
        expected = json.loads(args.triangular_manifest.read_text())
        actual = compact_triangular_manifest(results[0])
        triangular_manifest_check = compare_triangular_manifest(expected, actual)
        payload["triangular_manifest_check"] = triangular_manifest_check
    payload["all_ok"] = all(result["ok"] for result in results) and (
        triangular_manifest_check is None or triangular_manifest_check["ok"]
    )
    for result in results:
        full = result.get("full_verify", {})
        print(
            "m={m} scalar_ok={scalar_ok} triangular_ok={triangular_ok} "
            "table_ok={table_ok} expanded_valid={expanded_certificate_valid} "
            "full_ok={full_ok}".format(
                scalar_ok=result["scalar_units"]["ok"],
                triangular_ok=result["triangular_obligations"]["ok"],
                table_ok=result["zero_set_table"]["matches_shifted_zero_mask"],
                full_ok=full.get("ok", "skipped"),
                **result,
            )
        )
    if triangular_manifest_check is not None:
        print(
            "triangular_manifest_ok",
            triangular_manifest_check["ok"],
            "mismatches",
            triangular_manifest_check["mismatches"],
        )
    print(f"all_ok={payload['all_ok']}")
    if args.json_out:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
        print(f"wrote {args.json_out}")
    if not payload["all_ok"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
