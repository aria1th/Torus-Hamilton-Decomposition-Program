#!/usr/bin/env python3
"""Search simple zero-set cyclic kappa formulas for 4+2 bridge certificates."""

from __future__ import annotations

import argparse
import copy
import itertools
import json
from pathlib import Path

from verify_4plus2_allN_bridge_cert import (
    PERMS3,
    base_tuple,
    default_bundle_path,
    lambda1_direction,
    load_bundle,
    parse_only,
    verify_certificate,
)


PERM_INDEX = {perm: idx for idx, perm in enumerate(PERMS3)}


def zero_count(xs: tuple[int, int, int, int], m: int) -> int:
    full = (xs[0], xs[1], xs[2], xs[3], (-sum(xs)) % m)
    return sum(1 for value in full if value == 0)


def rotation_perm_index(r: int, reflected: bool) -> int:
    if reflected:
        perm = tuple((r - j) % 3 for j in range(3))
    else:
        perm = tuple((r + j) % 3 for j in range(3))
    return PERM_INDEX[perm]


def build_formula_kappa(
    m: int,
    *,
    a: int,
    b: int,
    c: int,
    d: int,
    reflected: bool,
) -> list[list[int]]:
    table = []
    for t in range(m):
        layer = []
        for base in range(m**4):
            xs = base_tuple(base, m)
            p_value = lambda1_direction(xs, 0, m)
            z_size = zero_count(xs, m)
            r = (a * (t % 3) + b * (p_value % 3) + c * (z_size % 3) + d) % 3
            layer.append(rotation_perm_index(r, reflected))
        table.append(layer)
    return table


def formula_label(a: int, b: int, c: int, d: int, reflected: bool) -> str:
    orientation = "reflected" if reflected else "cyclic"
    return f"{orientation}: r = {a}*t + {b}*p + {c}*z + {d} mod 3"


def test_formula(cert: dict, formula: dict) -> dict:
    candidate = copy.deepcopy(cert)
    candidate["kappa_perm_indices"] = build_formula_kappa(cert["m"], **formula)
    try:
        message, _summary = verify_certificate(candidate)
    except Exception as exc:
        return {"ok": False, "error": f"{type(exc).__name__}: {exc}"}
    return {"ok": True, "message": message}


def search_formulas(
    cert: dict, *, stop_after_first: bool, include_failures: bool
) -> dict:
    hits = []
    failures = []
    for reflected in (False, True):
        for a, b, c, d in itertools.product(range(3), repeat=4):
            formula = {"a": a, "b": b, "c": c, "d": d, "reflected": reflected}
            result = test_formula(cert, formula)
            record = {
                "formula": formula,
                "label": formula_label(a, b, c, d, reflected),
                "result": result,
            }
            if result["ok"]:
                hits.append(record)
                if stop_after_first:
                    return {"m": cert["m"], "hits": hits, "failures": failures}
            elif include_failures:
                failures.append(record)
    return {"m": cert["m"], "hits": hits, "failures": failures}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--bundle", type=Path, default=default_bundle_path())
    parser.add_argument("--only", help="comma-separated bundled moduli to test")
    parser.add_argument(
        "--all-hits", action="store_true", help="do not stop after first hit"
    )
    parser.add_argument("--include-failures", action="store_true")
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()

    payload = {
        "description": (
            "Search kappa(t,u)=rotation(a*t+b*p(Z(u))+c*|Z(u)|+d mod 3)."
        ),
        "searches": [
            search_formulas(
                cert,
                stop_after_first=not args.all_hits,
                include_failures=args.include_failures,
            )
            for cert in load_bundle(args.bundle, parse_only(args.only))
        ],
    }
    text = json.dumps(payload, indent=2, sort_keys=True)
    if args.json_out is None:
        print(text)
    else:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(text + "\n")
        print(f"wrote {args.json_out}")


if __name__ == "__main__":
    main()
