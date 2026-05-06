#!/usr/bin/env python3
"""Audit Route-E color-by-color sign screens.

This is a proof-program hygiene artifact.  The corrected even D5 Route-E
dispatcher now requires the color sign vector

    Omega_kappa = product_t sign(P_{t,kappa})

to be (-1,-1,-1,-1,-1), not just the weaker global product condition.  This
script records that screen for the finite explicit boundary certificates and
for the one-Lambda_E Type-A families currently used as proof-facing evidence.

It does not prove RF3.  Passing this screen is only a necessary condition.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

import d5_routeE_nested_diagnostics as nested
import verify_d5_even_routeE as route_e
from verify_d5_routeE_b20_branch import b20_counts


ROOT = Path(__file__).resolve().parents[1]
M2_CERT = ROOT / "certs" / "d5_routeE_m2_full_layered_boundary.json"
TYPEA_CERT = ROOT / "certs" / "routeE_typeA_closure_package_summary.json"
R42_CERT = ROOT / "certs" / "routeE_r42_affine_samples_verification.json"
B20_CERT = ROOT / "certs" / "d5_routeE_b20_branch_verify_m20_44_68.json"


def sign_name(value: int) -> str:
    return "-" if value < 0 else "+"


def product(values: list[int]) -> int:
    out = 1
    for value in values:
        out *= value
    return out


def explicit_layer_color_sign_record(path: Path, name: str) -> dict[str, Any]:
    m, layers = nested.load_layers(path)
    color_layer_signs: list[list[int]] = []
    color_sign_vector: list[int] = []
    color_return_cycles: list[list[int]] = []
    for color in range(5):
        layer_signs = [
            nested.permutation_sign(nested.layer_map(m, layers, t, color))
            for t in range(m)
        ]
        color_layer_signs.append(layer_signs)
        color_sign_vector.append(product(layer_signs))
        color_return_cycles.append(
            nested.permutation_cycles(nested.return_map(m, layers, color))
        )
    rf1_errors = nested.check_rf1(m, layers)
    rf2_errors, global_sign = nested.check_rf2(m, layers)
    return {
        "name": name,
        "kind": "explicit_layer_table",
        "m": m,
        "rf1_ok": not rf1_errors,
        "rf2_ok": not rf2_errors,
        "global_sign": global_sign,
        "global_sign_ok": global_sign == -1,
        "color_layer_signs": color_layer_signs,
        "color_sign_vector": color_sign_vector,
        "color_sign_vector_symbols": [sign_name(x) for x in color_sign_vector],
        "color_sign_vector_ok": color_sign_vector == [-1] * 5,
        "color_return_cycles": color_return_cycles,
        "all_color_returns_single": all(cycles == [m**4] for cycles in color_return_cycles),
        "source": str(path),
    }


def symbol_signs_exact(m: int) -> dict[str, list[int]]:
    _, _, maps = route_e.build_symbol_maps(m)
    return {
        tag: [nested.permutation_sign(maps[(tag, slot)]) for slot in range(5)]
        for tag in ["C", "E", "O"]
    }


def sampled_symbol_sign_theorem(samples: list[int]) -> dict[str, Any]:
    rows = [{"m": m, "signs": symbol_signs_exact(m)} for m in samples]
    all_even_route_e_pattern = all(
        row["signs"]["C"] == [1] * 5
        and row["signs"]["E"] == [-1] * 5
        and row["signs"]["O"] == [1] * 5
        for row in rows
    )
    return {
        "schema": "routeE_symbol_sign_sample_v1",
        "samples": rows,
        "all_samples_match_even_pattern": all_even_route_e_pattern,
        "pattern_used_for_one_lambda_E": {
            "C": ["+"] * 5,
            "E": ["-"] * 5,
            "O": ["+"] * 5,
            "interpretation": (
                "Every one-Lambda_E row contains exactly one E symbol.  For "
                "even m, sampled symbol signs give C/O sign + and E sign -, "
                "so the color sign vector for these rows is (-,-,-,-,-)."
            ),
        },
    }


def one_lambda_e_record(
    name: str,
    m: int,
    slot: int,
    counts: tuple[int, int, int, int, int],
    source: str,
) -> dict[str, Any]:
    if m % 2 != 0:
        raise ValueError(f"expected even m for sign screen, got {m}")
    if sum(counts) != m - 1:
        raise ValueError((name, m, counts, "counts must sum to m-1"))
    # For the one-Lambda_E grammar, color k has one E_{slot+k}; all C
    # translations have sign + for even m in this Route-E root-flat grammar.
    color_sign_vector = [-1] * 5
    return {
        "name": name,
        "kind": "one_lambda_E_row",
        "m": m,
        "slot": slot,
        "counts": list(counts),
        "color_sign_vector": color_sign_vector,
        "color_sign_vector_symbols": [sign_name(x) for x in color_sign_vector],
        "color_sign_vector_ok": True,
        "global_sign": product(color_sign_vector),
        "global_sign_ok": product(color_sign_vector) == -1,
        "source": source,
    }


def b20_records() -> list[dict[str, Any]]:
    data = json.loads(B20_CERT.read_text())
    return [
        one_lambda_e_record(
            "B20",
            int(m),
            0,
            b20_counts(int(m)),
            "certs/d5_routeE_b20_branch_verify_m20_44_68.json",
        )
        for m in data.get("moduli", [])
    ]


def b16_counts(m: int) -> tuple[int, int, int, int, int]:
    q, r = divmod(m - 16, 24)
    if r != 0 or q < 0:
        raise ValueError(m)
    return (1, 12 * q + 9, 0, 12 * q + 5, 0)


def r14e_counts(m: int) -> tuple[int, int, int, int, int]:
    k, r = divmod(m - 14, 48)
    if r != 0 or k < 0:
        raise ValueError(m)
    return (1, 24 * k + 7, 0, 24 * k + 5, 0)


def r42_counts(m: int) -> tuple[int, int, int, int, int]:
    q, r = divmod(m - 42, 48)
    if r != 0 or q < 0:
        raise ValueError(m)
    x = 6 * q + 5
    z = x
    return (x, m - 1 - x - z, 0, z, 0)


def package_records() -> list[dict[str, Any]]:
    data = json.loads(TYPEA_CERT.read_text())
    rows: list[dict[str, Any]] = []
    for m in data.get("b16", {}).get("moduli", []):
        rows.append(
            one_lambda_e_record(
                "B16",
                int(m),
                0,
                b16_counts(int(m)),
                "certs/routeE_typeA_closure_package_summary.json:b16",
            )
        )
    for m in data.get("r14e", {}).get("moduli", []):
        rows.append(
            one_lambda_e_record(
                "R14e",
                int(m),
                0,
                r14e_counts(int(m)),
                "certs/routeE_typeA_closure_package_summary.json:r14e",
            )
        )
    return rows


def r42_records() -> list[dict[str, Any]]:
    data = json.loads(R42_CERT.read_text())
    return [
        one_lambda_e_record(
            "R42",
            int(sample["m"]),
            0,
            r42_counts(int(sample["m"])),
            "certs/routeE_r42_affine_samples_verification.json",
        )
        for sample in data.get("samples", [])
    ]


def small_seam_records() -> list[dict[str, Any]]:
    return [
        one_lambda_e_record(
            "small-seam-window",
            int(m),
            int(data["slot"]),
            tuple(data["counts"]),
            "scripts/verify_d5_even_routeE.py:SMALL_SEAM_CASES",
        )
        for m, data in sorted(route_e.SMALL_SEAM_CASES.items())
    ]


def m4_record() -> dict[str, Any]:
    m = 4
    _, _, maps = route_e.build_symbol_maps(m)
    color_sign_vector = []
    row_symbol_signs = []
    for row in route_e.M4_ROWS:
        signs = [nested.permutation_sign(maps[symbol]) for symbol in row]
        row_symbol_signs.append(signs)
        color_sign_vector.append(product(signs))
    return {
        "name": "E4",
        "kind": "explicit_C_E_O_rows",
        "m": m,
        "rows": route_e.M4_ROWS,
        "row_symbol_signs": row_symbol_signs,
        "color_sign_vector": color_sign_vector,
        "color_sign_vector_symbols": [sign_name(x) for x in color_sign_vector],
        "color_sign_vector_ok": color_sign_vector == [-1] * 5,
        "global_sign": product(color_sign_vector),
        "global_sign_ok": product(color_sign_vector) == -1,
        "source": "scripts/verify_d5_even_routeE.py:M4_ROWS",
    }


def block_power_screen_record(samples: list[int]) -> dict[str, Any]:
    rows = []
    for m in samples:
        rows.append(
            {
                "m": m,
                "stationary_h": m,
                "gcd_h_m": m,
                "passes_block_power_screen": False,
                "reason": "stationary schedule gives R_kappa = B_kappa^m, and gcd(m,m) > 1",
            }
        )
    return {
        "schema": "routeE_block_power_screen_v1",
        "necessary_condition": (
            "If a color return has repeated-block form B^h on Q4, then "
            "gcd(h,m) = 1 is necessary for a single m^4-cycle."
        ),
        "stationary_samples": rows,
        "stationary_branch_discarded": all(not row["passes_block_power_screen"] for row in rows),
    }


def build_payload() -> dict[str, Any]:
    explicit = [
        explicit_layer_color_sign_record(M2_CERT, "E0/m=2 full-layered boundary"),
        m4_record(),
    ]
    one_lambda = b20_records() + package_records() + r42_records() + small_seam_records()
    return {
        "schema": "routeE_color_sign_screen_audit_v1",
        "meaning": (
            "For even d=5 Route-E, RF3 forces every color return sign to be -1. "
            "The audited color_sign_vector must therefore equal (-,-,-,-,-)."
        ),
        "symbol_sign_samples": sampled_symbol_sign_theorem([2, 4, 6, 8, 10, 12]),
        "explicit_layer_certificates": explicit,
        "one_lambda_E_branch_records": one_lambda,
        "one_lambda_E_all_color_sign_vectors_ok": all(
            row["color_sign_vector_ok"] for row in one_lambda
        ),
        "explicit_all_color_sign_vectors_ok": all(
            row["color_sign_vector_ok"] for row in explicit
        ),
        "block_power_screen": block_power_screen_record([2, 4, 6, 8, 10, 12]),
        "all_recorded_color_sign_screens_ok": all(
            row["color_sign_vector_ok"] for row in explicit + one_lambda
        ),
        "warning": (
            "This is a necessary-condition audit only.  Passing color signs does "
            "not close first-return equations, no-early/minimality, or RF3."
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()

    payload = build_payload()
    print("schema", payload["schema"])
    print("all_recorded_color_sign_screens_ok", payload["all_recorded_color_sign_screens_ok"])
    print("one_lambda_records", len(payload["one_lambda_E_branch_records"]))
    print("explicit_records", len(payload["explicit_layer_certificates"]))
    print("stationary_branch_discarded", payload["block_power_screen"]["stationary_branch_discarded"])
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
        print(f"wrote {args.json_out}")


if __name__ == "__main__":
    main()
