#!/usr/bin/env python3
"""Derive Lambda_E shifted-zero mask count polynomials.

The D5 one-Lambda_E defect layer is controlled by five predicates

    z4 = z3, z3 = z2, z2 = z1, z1 = 0, z4 = 0.

These are the edge equalities of a 5-cycle whose fifth vertex is the fixed
zero node.  For a set of required equalities S, the number of assignments is
`m^(components(S)-1)`: the component containing the fixed zero is fixed and all
other components are free.

This script uses inclusion-exclusion over supersets to derive exact
polynomials for each shifted-zero mask.  It then groups masks through the
Lambda_E local row rule and the adjacent-switch row words used by
`analyze_d5_routeE_layer_switches.py`.

No external CAS is required; polynomials are represented as integer
coefficient dictionaries in the variable `m`.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter, deque
from functools import lru_cache
from pathlib import Path

import analyze_d5_routeE_layer_switches as switches
import analyze_d5_routeE_defect_layer as defect


Poly = dict[int, int]


EDGES = [
    (4, 3),  # z4 = z3
    (3, 2),  # z3 = z2
    (2, 1),  # z2 = z1
    (1, 0),  # z1 = 0
    (4, 0),  # z4 = 0
]


def poly_add(a: Poly, b: Poly, sign: int = 1) -> Poly:
    out = dict(a)
    for deg, coeff in b.items():
        out[deg] = out.get(deg, 0) + sign * coeff
        if out[deg] == 0:
            del out[deg]
    return out


def poly_mul_const(a: Poly, c: int) -> Poly:
    if c == 0:
        return {}
    return {deg: coeff * c for deg, coeff in a.items() if coeff * c}


def poly_eval(a: Poly, m: int) -> int:
    return sum(coeff * (m**deg) for deg, coeff in a.items())


def poly_text(a: Poly) -> str:
    if not a:
        return "0"
    parts: list[str] = []
    for deg in sorted(a, reverse=True):
        coeff = a[deg]
        sign = "-" if coeff < 0 else "+"
        c = abs(coeff)
        if deg == 0:
            atom = str(c)
        elif deg == 1:
            atom = "m" if c == 1 else f"{c}*m"
        else:
            atom = f"m^{deg}" if c == 1 else f"{c}*m^{deg}"
        parts.append((sign, atom))
    first_sign, first_atom = parts[0]
    text = ("" if first_sign == "+" else "-") + first_atom
    for sign, atom in parts[1:]:
        text += f" {sign} {atom}"
    return text


def poly_json(a: Poly) -> dict[str, int]:
    return {str(deg): coeff for deg, coeff in sorted(a.items())}


def popcount(mask: int) -> int:
    return mask.bit_count()


def components_for_edges(mask: int) -> int:
    parent = list(range(5))

    def find(x: int) -> int:
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def union(a: int, b: int) -> None:
        ra, rb = find(a), find(b)
        if ra != rb:
            parent[rb] = ra

    for bit, (a, b) in enumerate(EDGES):
        if mask & (1 << bit):
            union(a, b)
    return len({find(i) for i in range(5)})


def all_supersets(mask: int) -> list[int]:
    missing = [bit for bit in range(5) if not (mask & (1 << bit))]
    out = []
    for sub in range(1 << len(missing)):
        t = mask
        for i, bit in enumerate(missing):
            if sub & (1 << i):
                t |= 1 << bit
        out.append(t)
    return out


@lru_cache(maxsize=None)
def exact_mask_poly(mask: int) -> tuple[tuple[int, int], ...]:
    total: Poly = {}
    for sup in all_supersets(mask):
        sign = -1 if (popcount(sup) - popcount(mask)) % 2 else 1
        # Required equalities in `sup` leave components-1 free coordinates,
        # since vertex 0 is fixed to the zero value.
        poly = {components_for_edges(sup) - 1: 1}
        total = poly_add(total, poly, sign)
    return tuple(sorted(total.items()))


def exact_poly(mask: int) -> Poly:
    return dict(exact_mask_poly(mask))


def derive_payload() -> dict:
    words = switches.shortest_words_from(defect.BULK_ROW)
    row_polys: dict[switches.Row, Poly] = {}
    rank_totals: dict[int, Poly] = {0: {}, 1: {}, 2: {}, 3: {}}
    modal_poly: Poly = {}
    mask_entries: list[dict] = []

    for mask in range(32):
        poly = exact_poly(mask)
        if not poly:
            mask_entries.append(
                {
                    "mask": f"{mask:05b}",
                    "mask_int": mask,
                    "polynomial": "0",
                    "coefficients": {},
                    "row": None,
                    "word": None,
                    "reachable": False,
                }
            )
            continue
        if mask not in defect.routee.CANON:
            raise RuntimeError(
                f"mask {mask:05b} has nonzero count {poly_text(poly)} "
                "but is not in the Lambda_E canonical mask table"
            )
        row = defect.row_for_mask(mask)
        word = words[row]
        row_polys[row] = poly_add(row_polys.get(row, {}), poly)
        if row == defect.BULK_ROW:
            modal_poly = poly_add(modal_poly, poly)
        for rank, _ in word:
            rank_totals[rank] = poly_add(rank_totals[rank], poly)
        mask_entries.append(
            {
                "mask": f"{mask:05b}",
                "mask_int": mask,
                "polynomial": poly_text(poly),
                "coefficients": poly_json(poly),
                "row": list(row),
                "word": switches.word_text(word),
                "word_ranks": [rank for rank, _ in word],
                "reachable": True,
            }
        )

    total_nonmodal: Poly = {4: 1}
    total_nonmodal = poly_add(total_nonmodal, modal_poly, sign=-1)
    sample_moduli = [6, 8, 10, 12, 14, 16, 18, 20]
    checks = []
    for m in sample_moduli:
        checks.append(
            {
                "m": m,
                "modal": poly_eval(modal_poly, m),
                "nonmodal": poly_eval(total_nonmodal, m),
                "rank_totals": {
                    str(rank): poly_eval(rank_totals[rank], m) for rank in range(4)
                },
            }
        )
    return {
        "schema": "d5_lambdaE_mask_polynomials_v1",
        "description": (
            "Exact shifted-zero mask count polynomials for the D5 Route-E "
            "Lambda_E defect layer, derived by inclusion-exclusion over the "
            "5-cycle equality arrangement."
        ),
        "edges": EDGES,
        "bulk_row": list(defect.BULK_ROW),
        "mask_entries": mask_entries,
        "modal_count": {
            "polynomial": poly_text(modal_poly),
            "coefficients": poly_json(modal_poly),
        },
        "nonmodal_count": {
            "polynomial": poly_text(total_nonmodal),
            "coefficients": poly_json(total_nonmodal),
        },
        "rank_totals": {
            str(rank): {
                "polynomial": poly_text(rank_totals[rank]),
                "coefficients": poly_json(rank_totals[rank]),
            }
            for rank in range(4)
        },
        "sample_checks": checks,
    }


def print_payload(payload: dict) -> None:
    print("mask,poly,row,word")
    for entry in payload["mask_entries"]:
        if not entry["reachable"]:
            print(f"{entry['mask']},0,unreachable,unreachable")
            continue
        print(
            f"{entry['mask']},{entry['polynomial']},"
            f"\"{tuple(entry['row'])}\",\"{entry['word']}\""
        )

    print()
    print(f"modal_count={payload['modal_count']['polynomial']}")
    print(f"nonmodal_count={payload['nonmodal_count']['polynomial']}")
    for rank in range(4):
        print(
            f"rank_{rank}_total="
            f"{payload['rank_totals'][str(rank)]['polynomial']}"
        )

    for check in payload["sample_checks"]:
        values = {
            "modal": check["modal"],
            "nonmodal": check["nonmodal"],
            **{
                f"rank{rank}": check["rank_totals"][str(rank)]
                for rank in range(4)
            },
        }
        print(f"check m={check['m']} {values}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--json-out", type=Path, help="write symbolic derivation JSON")
    args = parser.parse_args()

    payload = derive_payload()
    print_payload(payload)
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2) + "\n")
        print(f"wrote {args.json_out}")


if __name__ == "__main__":
    main()
