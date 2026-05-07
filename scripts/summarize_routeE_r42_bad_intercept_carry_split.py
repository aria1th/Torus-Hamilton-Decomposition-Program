#!/usr/bin/env python3
"""Mine one-step carry splits for the R42 bad qtime-intercept atoms.

The preceding c-band qtime atom diagnostic shows that

  edge + interval length + c-band + u mod 6

is enough to make all sampled qtime slopes affine, but not enough for all
qtime intercepts.  This script focuses only on the bad intercept atoms and
tests small carry features such as threshold indicators in j and residue
indicators.  It is sampled diagnostic evidence, not a no-early proof.
"""

from __future__ import annotations

import argparse
import json
import tempfile
from fractions import Fraction
from pathlib import Path
from typing import Any, Callable

import summarize_routeE_r42_carry_qtime_atoms as qta


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_QTIME_ATOMS = ROOT / "certs" / "routeE_r42_carry_qtime_atoms.json"
DEFAULT_BIN = qta.DEFAULT_BIN


Feature = tuple[str, Callable[[dict[str, Any]], int]]


def parse_q_values(spec: str) -> list[int]:
    if ":" in spec:
        lo, hi = spec.split(":", 1)
        return list(range(int(lo), int(hi) + 1))
    return [int(part) for part in spec.split(",") if part]


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


def load_bad_atoms(path: Path) -> dict[str, list[str]]:
    data = json.loads(path.read_text())
    out: dict[str, list[str]] = {}
    for branch in data.get("generic_subbranches", []):
        out[branch["name"]] = list(branch.get("bad_intercept_atoms", []))
    return out


def collect_bad_rows(
    q_values: list[int],
    binary: Path,
    bad_atoms: set[str],
    compile_binary: bool,
) -> list[dict[str, Any]]:
    if compile_binary:
        qta.r42.compile_checker(binary)
    rows: list[dict[str, Any]] = []
    with tempfile.TemporaryDirectory(prefix="routeE-r42-bad-carry-") as tmp:
        tmpdir = Path(tmp)
        for q in q_values:
            s = q // 2 if q % 2 == 0 else (q - 1) // 2
            c = 6 * q + 5
            m = 8 * c + 2
            branch = "R42-even-q" if q % 2 == 0 else "R42-odd-q"
            for row in qta.collect_rows(binary, q, tmpdir):
                if row["atom"] in bad_atoms:
                    row["q"] = q
                    row["s"] = s
                    row["c"] = c
                    row["m"] = m
                    row["branch"] = branch
                    rows.append(row)
    return rows


def base_features(row: dict[str, Any]) -> list[int]:
    s = row["s"]
    j = row["j"]
    return [1, s, s * s, j, s * j]


def candidate_features() -> list[Feature]:
    features: list[Feature] = []
    # The feature is multiplied by m so that a coefficient ±1 corresponds to a
    # single modular wrap/carry in the intercept.
    for off in range(-6, 9):
        features.append(
            (
                f"m*1[j>=s{off:+d}]",
                lambda row, off=off: row["m"] * int(row["j"] >= row["s"] + off),
            )
        )
        features.append(
            (
                f"m*1[j>s{off:+d}]",
                lambda row, off=off: row["m"] * int(row["j"] > row["s"] + off),
            )
        )
        features.append(
            (
                f"m*1[j>=2s{off:+d}]",
                lambda row, off=off: row["m"] * int(row["j"] >= 2 * row["s"] + off),
            )
        )
        features.append(
            (
                f"m*1[j>2s{off:+d}]",
                lambda row, off=off: row["m"] * int(row["j"] > 2 * row["s"] + off),
            )
        )
    for mod in (2, 3, 4, 5, 6):
        for rem in range(mod):
            features.append(
                (
                    f"m*1[j%{mod}={rem}]",
                    lambda row, mod=mod, rem=rem: row["m"] * int(row["j"] % mod == rem),
                )
            )
    return features


def fit_with_features(
    rows: list[dict[str, Any]],
    features: list[Feature],
    max_pair_hits: int = 12,
) -> dict[str, Any]:
    base_names = ["1", "s", "s^2", "j", "s*j"]
    base_fit = solve_linear([(base_features(row), row["qtime_intercept"]) for row in rows])
    one_hits = []
    for name, fn in features:
        names = base_names + [name]
        fit = solve_linear(
            [
                (base_features(row) + [fn(row)], row["qtime_intercept"])
                for row in rows
            ]
        )
        if fit is not None:
            one_hits.append({"feature": name, "formula": format_linear(fit, names)})
    pair_hits = []
    if not one_hits:
        for i, (name1, fn1) in enumerate(features):
            for name2, fn2 in features[i + 1 :]:
                names = base_names + [name1, name2]
                fit = solve_linear(
                    [
                        (base_features(row) + [fn1(row), fn2(row)], row["qtime_intercept"])
                        for row in rows
                    ]
                )
                if fit is not None:
                    pair_hits.append(
                        {
                            "features": [name1, name2],
                            "formula": format_linear(fit, names),
                        }
                    )
                    if len(pair_hits) >= max_pair_hits:
                        break
            if len(pair_hits) >= max_pair_hits:
                break
    return {
        "base_fit": base_fit is not None,
        "one_feature_hit_count": len(one_hits),
        "one_feature_hits": one_hits[:20],
        "two_feature_hit_count": len(pair_hits),
        "two_feature_hits": pair_hits[:max_pair_hits],
    }


def build_summary(q_values: list[int], qtime_atoms_path: Path, binary: Path, compile_binary: bool) -> dict[str, Any]:
    bad_by_branch = load_bad_atoms(qtime_atoms_path)
    bad_atoms = sorted({atom for atoms in bad_by_branch.values() for atom in atoms})
    rows = collect_bad_rows(q_values, binary, set(bad_atoms), compile_binary)
    features = candidate_features()
    branches = []
    for branch_name, atoms in sorted(bad_by_branch.items()):
        branch_rows = [row for row in rows if row["branch"] == branch_name]
        atom_summaries = []
        for atom in atoms:
            atom_rows = [row for row in branch_rows if row["atom"] == atom]
            fit = fit_with_features(atom_rows, features)
            atom_summaries.append(
                {
                    "atom": atom,
                    "sample_count": len(atom_rows),
                    "j_values": sorted({row["j"] for row in atom_rows}),
                    "q_values": sorted({row["q"] for row in atom_rows}),
                    **fit,
                }
            )
        branches.append(
            {
                "name": branch_name,
                "bad_atom_count": len(atoms),
                "rows": len(branch_rows),
                "atoms_with_one_feature_hit": sum(
                    1 for item in atom_summaries if item["one_feature_hit_count"] > 0
                ),
                "atoms_with_two_feature_hit": sum(
                    1 for item in atom_summaries if item["two_feature_hit_count"] > 0
                ),
                "atom_summaries": atom_summaries,
            }
        )
    return {
        "schema": "routeE_r42_bad_intercept_carry_split_v1",
        "family": "R42, c=6*q+5, m=8*c+2, x=z=c",
        "q_values": q_values,
        "bad_atom_count": len(bad_atoms),
        "row_count": len(rows),
        "candidate_feature_count": len(features),
        "generic_subbranches": branches,
        "summary": {
            "all_bad_atoms_have_one_feature_hit": all(
                branch["atoms_with_one_feature_hit"] == branch["bad_atom_count"]
                for branch in branches
            ),
            "all_bad_atoms_have_one_or_two_feature_hit": all(
                branch["atoms_with_one_feature_hit"] + branch["atoms_with_two_feature_hit"]
                == branch["bad_atom_count"]
                for branch in branches
            ),
            "branch_one_feature_hits": {
                branch["name"]: branch["atoms_with_one_feature_hit"] for branch in branches
            },
            "branch_two_feature_hits": {
                branch["name"]: branch["atoms_with_two_feature_hit"] for branch in branches
            },
        },
        "promotion_impact": {
            "closes_residue": False,
            "pointwise_equations_closed": False,
            "no_early_closed": False,
            "diagnosis": (
                "Mines small carry features for the nine qtime-intercept atoms "
                "that the first c-band atom model misses.  A positive hit is "
                "a candidate for the next refined transducer state, not a "
                "proof of no-early."
            ),
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--q-values", default="6:9")
    parser.add_argument("--qtime-atoms", type=Path, default=DEFAULT_QTIME_ATOMS)
    parser.add_argument("--binary", type=Path, default=DEFAULT_BIN)
    parser.add_argument("--no-compile", action="store_true")
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()
    q_values = parse_q_values(args.q_values)
    payload = build_summary(
        q_values=q_values,
        qtime_atoms_path=args.qtime_atoms,
        binary=args.binary,
        compile_binary=not args.no_compile,
    )
    print("schema", payload["schema"])
    print("q_values", payload["q_values"])
    print("row_count", payload["row_count"])
    print("bad_atom_count", payload["bad_atom_count"])
    print("summary", payload["summary"])
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
        print(f"wrote {args.json_out}")


if __name__ == "__main__":
    main()
