#!/usr/bin/env python3
"""Fit qtime coefficients on R42 c-band support atoms.

Input states are the c-band/u-mod-6 support atoms from
summarize_routeE_r42_carry_support_atoms.py.  This script tests the next
natural clock-carry hypothesis:

  qtime_slope = affine(s)
  qtime_intercept = A + B*s + C*s^2 + D*j + E*s*j

on every sampled atom, separately on the even-q and odd-q branches.

This is sampled symbolic evidence, not a no-early proof.
"""

from __future__ import annotations

import argparse
import json
import tempfile
from fractions import Fraction
from pathlib import Path
from typing import Any

import summarize_routeE_r42_boundary_quotient as r42
import summarize_routeE_r42_boundary_block_transducer as bt
from summarize_routeE_r42_mod96_edge_partitions import affine_coeffs, intervals
from summarize_routeE_r42_carry_support_atoms import atom_key, parse_range


DEFAULT_BIN = Path(tempfile.gettempdir()) / "routeE_allpair_cpp_v1_2"


def solve_linear(points: list[tuple[list[int], int]]) -> list[Fraction] | None:
    if not points:
        return None
    width = len(points[0][0])
    rows = [[Fraction(x) for x in features] + [Fraction(y)] for features, y in points]
    pivot_cols: list[int] = []
    r = 0
    for c in range(width):
        pivot = next((i for i in range(r, len(rows)) if rows[i][c] != 0), None)
        if pivot is None:
            continue
        rows[r], rows[pivot] = rows[pivot], rows[r]
        scale = rows[r][c]
        rows[r] = [value / scale for value in rows[r]]
        for i in range(len(rows)):
            if i == r:
                continue
            factor = rows[i][c]
            if factor:
                rows[i] = [a - factor * b for a, b in zip(rows[i], rows[r])]
        pivot_cols.append(c)
        r += 1
        if r == len(rows):
            break
    for row in rows:
        if all(row[c] == 0 for c in range(width)) and row[-1] != 0:
            return None
    coeffs = [Fraction(0) for _ in range(width)]
    for row_index, col in enumerate(pivot_cols):
        coeffs[col] = rows[row_index][-1]
    if any(sum(coeff * x for coeff, x in zip(coeffs, features)) != y for features, y in points):
        return None
    return coeffs


def format_fraction(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def format_linear(coeffs: list[Fraction] | None, names: list[str]) -> str | None:
    if coeffs is None:
        return None
    terms = []
    for coeff, name in zip(coeffs, names):
        if coeff == 0:
            continue
        coeff_text = format_fraction(abs(coeff))
        if name == "1":
            term = coeff_text
        elif coeff_text == "1":
            term = name
        else:
            term = f"{coeff_text}*{name}"
        if not terms:
            terms.append(term if coeff > 0 else f"-{term}")
        else:
            terms.append((" + " if coeff > 0 else " - ") + term)
    return "".join(terms) if terms else "0"


def collect_rows(binary: Path, q: int, workdir: Path) -> list[dict[str, Any]]:
    c = 6 * q + 5
    m = 8 * c + 2
    cap = max(10_000, 10 * m * m)
    csv_path = workdir / f"r42_carry_qtime_atoms_q{q}.csv"
    proc = r42.subprocess.run(
        [str(binary), "dump-csv", str(m), str(c), str(c), str(cap), str(csv_path)],
        cwd=r42.REPO,
        text=True,
        stdout=r42.subprocess.PIPE,
        stderr=r42.subprocess.PIPE,
        check=False,
    )
    if proc.returncode != 0:
        raise RuntimeError(proc.stderr)
    rows = r42.load_rows(csv_path)
    blocks = bt.block_rows(r42.boundary_return_rows(rows), m)
    by_node: dict[tuple[str, int], int] = {}
    by_member: dict[tuple[str, int], dict[str, Any]] = {}
    for index, block in enumerate(blocks):
        for member in block["_members"]:
            key = (member["src_label"], member["src_a"])
            by_node[key] = index
            by_member[key] = member
    groups: dict[tuple[int, int], list[dict[str, Any]]] = {}
    for key, member in by_member.items():
        src_block = by_node[key]
        dst_block = by_node[(member["dst_label"], member["dst_a"])]
        groups.setdefault((src_block, dst_block), []).append(member)

    out = []
    for (src, dst), members in sorted(groups.items()):
        members = sorted(members, key=lambda row: row["src_a"])
        if affine_coeffs([(member["src_a"], member["qtime"]) for member in members]):
            continue
        for lo, hi in intervals([member["src_a"] for member in members]):
            sub = [member for member in members if lo <= member["src_a"] <= hi]
            coeffs = affine_coeffs([(member["src_a"], member["qtime"]) for member in sub])
            if coeffs is None:
                continue
            u_lo = lo % c
            u_hi = hi % c
            u_lo_mod6 = u_lo % 6
            u_hi_mod6 = u_hi % 6
            row = {
                "src": src,
                "dst": dst,
                "lo": lo,
                "hi": hi,
                "length": hi - lo + 1,
                "band_lo": lo // c,
                "band_hi": hi // c,
                "u_lo_mod6": u_lo_mod6,
                "u_hi_mod6": u_hi_mod6,
                "j": (u_lo - u_lo_mod6) // 6,
                "qtime_slope": coeffs[0],
                "qtime_intercept": coeffs[1],
            }
            row["atom"] = atom_key(row)
            out.append(row)
    return out


def branch_summary(all_rows: list[dict[str, Any]], parity: int) -> dict[str, Any]:
    name = "R42-even-q" if parity == 0 else "R42-odd-q"
    rows = [row for row in all_rows if row["q"] % 2 == parity]
    atom_keys = sorted({row["atom"] for row in rows})
    atoms = []
    bad_slope = []
    bad_intercept = []
    for key in atom_keys:
        atom_rows = [row for row in rows if row["atom"] == key]
        slope_fit = solve_linear(
            [([1, row["s"]], row["qtime_slope"]) for row in atom_rows]
        )
        intercept_fit = solve_linear(
            [
                ([1, row["s"], row["s"] * row["s"], row["j"], row["s"] * row["j"]], row["qtime_intercept"])
                for row in atom_rows
            ]
        )
        if slope_fit is None:
            bad_slope.append(key)
        if intercept_fit is None:
            bad_intercept.append(key)
        first = atom_rows[0]
        atoms.append(
            {
                "atom": key,
                "src": first["src"],
                "dst": first["dst"],
                "length": first["length"],
                "band_lo": first["band_lo"],
                "band_hi": first["band_hi"],
                "u_lo_mod6": first["u_lo_mod6"],
                "u_hi_mod6": first["u_hi_mod6"],
                "sample_count": len(atom_rows),
                "qtime_slope_formula": format_linear(slope_fit, ["1", "s"]),
                "qtime_intercept_formula": format_linear(
                    intercept_fit,
                    ["1", "s", "s^2", "j", "s*j"],
                ),
            }
        )
    return {
        "name": name,
        "parity": parity,
        "atom_key_count": len(atom_keys),
        "all_qtime_slopes_affine_in_s": not bad_slope,
        "all_qtime_intercepts_quadratic_s_linear_j": not bad_intercept,
        "bad_slope_atoms": bad_slope[:20],
        "bad_intercept_atoms": bad_intercept[:20],
        "atoms": atoms,
    }


def build_summary(q_values: list[int], binary: Path, compile_binary: bool) -> dict[str, Any]:
    if compile_binary:
        r42.compile_checker(binary)
    all_rows = []
    with tempfile.TemporaryDirectory(prefix="routeE-r42-carry-qtime-atoms-") as tmp:
        for q in q_values:
            s = q // 2 if q % 2 == 0 else (q - 1) // 2
            for row in collect_rows(binary, q, Path(tmp)):
                row["q"] = q
                row["s"] = s
                all_rows.append(row)
    branches = [branch_summary(all_rows, 0), branch_summary(all_rows, 1)]
    return {
        "schema": "routeE_r42_carry_qtime_atoms_v1",
        "family": "R42, c=6*q+5, m=8*c+2, x=z=c",
        "q_values": q_values,
        "generic_subbranches": branches,
        "summary": {
            "row_count": len(all_rows),
            "all_branch_qtime_slopes_affine": all(
                branch["all_qtime_slopes_affine_in_s"] for branch in branches
            ),
            "all_branch_qtime_intercepts_fit": all(
                branch["all_qtime_intercepts_quadratic_s_linear_j"] for branch in branches
            ),
            "branch_atom_key_counts": {
                branch["name"]: branch["atom_key_count"] for branch in branches
            },
        },
        "promotion_impact": {
            "closes_residue": False,
            "pointwise_equations_closed": False,
            "no_early_closed": False,
            "diagnosis": (
                "On sampled witnesses, qtime slopes fit on every c-band "
                "support atom, but the first intercept model still fails on "
                "nine atoms in each parity branch.  This is a useful negative "
                "diagnostic: the transducer needs one more carry split."
            ),
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--q-values", default="6:9")
    parser.add_argument("--binary", type=Path, default=DEFAULT_BIN)
    parser.add_argument("--no-compile", action="store_true")
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()
    payload = build_summary(parse_range(args.q_values), args.binary, not args.no_compile)
    print("schema", payload["schema"])
    print("row_count", payload["summary"]["row_count"])
    print("all_branch_qtime_slopes_affine", payload["summary"]["all_branch_qtime_slopes_affine"])
    print("all_branch_qtime_intercepts_fit", payload["summary"]["all_branch_qtime_intercepts_fit"])
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
        print(f"wrote {args.json_out}")


if __name__ == "__main__":
    main()
