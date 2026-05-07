#!/usr/bin/env python3
"""Search phase-shifted carry gates for the R42-odd unresolved atom.

The fixed even-q feature model

  threshold + 1[j mod 5 = 0] + 1[j mod 6 = 5]

does not explain the odd-q samples for the unresolved atom.  This script tests
the natural next hypothesis: the odd branch uses phase-shifted residue gates

  ±j + alpha*q + beta == 0 mod 5
  ±j + gamma*q + delta == 0 mod 6

plus a threshold/reversed-threshold carry.
"""

from __future__ import annotations

import argparse
import itertools
import json
from fractions import Fraction
from pathlib import Path
from typing import Any, Callable


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_INPUT = (
    ROOT / "certs" / "routeE_r42_unresolved_atom_20_feature_depth_odd_q7_9_11.json"
)
ATOM = "20->26|L1|B7:7|R0:0"


Feature = tuple[str, Callable[[dict[str, int]], int]]


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


def modinv(value: int, prime: int) -> int:
    return pow(value % prime, prime - 2, prime)


def add_basis_vector(
    basis: list[tuple[int, tuple[int, ...]]],
    vector: tuple[int, ...],
    prime: int,
) -> bool:
    row = list(vector)
    for pivot, basis_row in basis:
        factor = row[pivot]
        if factor:
            row = [(a - factor * b) % prime for a, b in zip(row, basis_row)]
    pivot = next((i for i, value in enumerate(row) if value), None)
    if pivot is None:
        return False
    scale = modinv(row[pivot], prime)
    row = [(value * scale) % prime for value in row]
    for index, (old_pivot, old_row) in enumerate(basis):
        factor = old_row[pivot]
        if factor:
            basis[index] = (
                old_pivot,
                tuple((a - factor * b) % prime for a, b in zip(old_row, row)),
            )
    basis.append((pivot, tuple(row)))
    basis.sort(key=lambda item: item[0])
    return True


def reduce_mod(
    basis: list[tuple[int, tuple[int, ...]]],
    vector: tuple[int, ...],
    prime: int,
) -> tuple[int, ...]:
    row = list(vector)
    for pivot, basis_row in basis:
        factor = row[pivot]
        if factor:
            row = [(a - factor * b) % prime for a, b in zip(row, basis_row)]
    return tuple(row)


def residual_vectors_mod(
    points: list[dict[str, int]],
    features: list[Feature],
    prime: int,
) -> tuple[tuple[int, ...], list[tuple[int, ...]]]:
    base_basis: list[tuple[int, tuple[int, ...]]] = []
    base_columns = [
        tuple(base(row)[column] % prime for row in points)
        for column in range(5)
    ]
    for column in base_columns:
        add_basis_vector(base_basis, column, prime)
    y_residual = reduce_mod(
        base_basis,
        tuple(row["y"] % prime for row in points),
        prime,
    )
    feature_residuals = [
        reduce_mod(
            base_basis,
            tuple(fn(row) % prime for row in points),
            prime,
        )
        for _, fn in features
    ]
    return y_residual, feature_residuals


def modular_candidate_filter(
    points: list[dict[str, int]],
    feature_groups: list[list[Feature]],
    primes: list[int],
) -> tuple[list[tuple[int, int, int]], dict[str, Any]]:
    all_features = [feature for group in feature_groups for feature in group]
    offsets: list[int] = []
    total = 0
    for group in feature_groups:
        offsets.append(total)
        total += len(group)

    per_prime: list[tuple[tuple[int, ...], list[tuple[int, ...]], int]] = []
    for prime in primes:
        y_residual, feature_residuals = residual_vectors_mod(points, all_features, prime)
        per_prime.append((y_residual, feature_residuals, prime))

    survivors: list[tuple[int, int, int]] = []
    checked = 0
    for i in range(len(feature_groups[0])):
        for j in range(len(feature_groups[1])):
            for k in range(len(feature_groups[2])):
                checked += 1
                ok = True
                absolute = (offsets[0] + i, offsets[1] + j, offsets[2] + k)
                for y_residual, feature_residuals, prime in per_prime:
                    span_basis: list[tuple[int, tuple[int, ...]]] = []
                    for index in absolute:
                        add_basis_vector(span_basis, feature_residuals[index], prime)
                    if reduce_mod(span_basis, y_residual, prime) != tuple(
                        0 for _ in y_residual
                    ):
                        ok = False
                        break
                if ok:
                    survivors.append((i, j, k))
    return survivors, {
        "checked_candidate_count": checked,
        "modular_survivor_count": len(survivors),
        "screen_primes": primes,
    }


def fmt_frac(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def fmt_linear(coeffs: list[Fraction] | None, names: list[str]) -> str | None:
    if coeffs is None:
        return None
    terms = []
    for coeff, name in zip(coeffs, names):
        if coeff == 0:
            continue
        mag = fmt_frac(abs(coeff))
        if name == "1":
            term = mag
        elif mag == "1":
            term = name
        else:
            term = f"{mag}*{name}"
        if not terms:
            terms.append(term if coeff > 0 else f"-{term}")
        else:
            terms.append((" + " if coeff > 0 else " - ") + term)
    return "".join(terms) if terms else "0"


def load_points(path: Path) -> list[dict[str, int]]:
    data = json.loads(path.read_text())
    for branch in data.get("generic_subbranches", []):
        if branch.get("name") == "R42-odd-q":
            return [
                {
                    "q": int(point["q"]),
                    "s": int(point["s"]),
                    "j": int(point["j"]),
                    "m": 48 * int(point["q"]) + 42,
                    "y": int(point["qtime_intercept"]),
                }
                for point in branch.get("qj_points", [])
            ]
    return []


def base(row: dict[str, int]) -> list[int]:
    s = row["s"]
    j = row["j"]
    return [1, s, s * s, j, s * j]


def threshold_features() -> list[Feature]:
    out: list[Feature] = []
    for off in range(-8, 13):
        out.append(
            (
                f"m*1[j>s{off:+d}]",
                lambda row, off=off: row["m"] * int(row["j"] > row["s"] + off),
            )
        )
        out.append(
            (
                f"m*1[j>=s{off:+d}]",
                lambda row, off=off: row["m"] * int(row["j"] >= row["s"] + off),
            )
        )
        out.append(
            (
                f"m*1[q-j>s{off:+d}]",
                lambda row, off=off: row["m"] * int(row["q"] - row["j"] > row["s"] + off),
            )
        )
        out.append(
            (
                f"m*1[q-j>=s{off:+d}]",
                lambda row, off=off: row["m"] * int(row["q"] - row["j"] >= row["s"] + off),
            )
        )
    return out


def residue_features(modulus: int) -> list[Feature]:
    out: list[Feature] = []
    for sign in (1, -1):
        sign_text = "j" if sign == 1 else "-j"
        for alpha in range(modulus):
            for beta in range(modulus):
                out.append(
                    (
                        f"m*1[({sign_text}+{alpha}q+{beta})%{modulus}=0]",
                        lambda row, sign=sign, alpha=alpha, beta=beta, modulus=modulus: row["m"]
                        * int((sign * row["j"] + alpha * row["q"] + beta) % modulus == 0),
                    )
                )
    return out


def fit(points: list[dict[str, int]], features: list[Feature]) -> dict[str, Any]:
    base_names = ["1", "s", "s^2", "j", "s*j"]
    names = base_names + [name for name, _ in features]
    coeffs = solve_linear(
        [
            (base(row) + [fn(row) for _, fn in features], row["y"])
            for row in points
        ]
    )
    return {
        "features": [name for name, _ in features],
        "formula": fmt_linear(coeffs, names),
        "hit": coeffs is not None,
    }


def build_summary(path: Path, max_hits: int) -> dict[str, Any]:
    points = load_points(path)
    th = threshold_features()
    mod5 = residue_features(5)
    mod6 = residue_features(6)
    hits = []
    survivors, screen = modular_candidate_filter(
        points,
        [th, mod5, mod6],
        [1_000_000_007, 1_000_000_009],
    )
    # Test the mathematically motivated depth-three form:
    # one threshold-like carry, one mod-5 phase, one mod-6 phase.
    for i, j, k in survivors:
        f1, f2, f3 = th[i], mod5[j], mod6[k]
        result = fit(points, [f1, f2, f3])
        if result["hit"]:
            hits.append(result)
            if len(hits) >= max_hits:
                break
    return {
        "schema": "routeE_r42_odd_phase_shifted_carry_v1",
        "atom": ATOM,
        "source_artifact": str(path),
        "sample_count": len(points),
        "q_values": sorted({point["q"] for point in points}),
        "j_values": sorted({point["j"] for point in points}),
        "search_space": {
            "threshold_feature_count": len(th),
            "mod5_feature_count": len(mod5),
            "mod6_feature_count": len(mod6),
            "depth_three_candidate_count": len(th) * len(mod5) * len(mod6),
            **screen,
        },
        "hit_count": len(hits),
        "hits": hits,
        "promotion_impact": {
            "closes_residue": False,
            "pointwise_equations_closed": False,
            "no_early_closed": False,
            "diagnosis": (
                "Tests whether R42-odd is a phase-shifted version of the "
                "R42-even depth-three carry grammar on the unresolved atom."
            ),
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, default=DEFAULT_INPUT)
    parser.add_argument("--max-hits", type=int, default=12)
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()
    payload = build_summary(args.input, args.max_hits)
    print("schema", payload["schema"])
    print("sample_count", payload["sample_count"])
    print("q_values", payload["q_values"])
    print("hit_count", payload["hit_count"])
    if payload["hits"]:
        print("first_hit", payload["hits"][0])
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
        print(f"wrote {args.json_out}")


if __name__ == "__main__":
    main()
