#!/usr/bin/env python3
"""Profile the D5 even Route-E B20 branch traces.

This is a proof-discovery artifact.  The B20 branch verifier proves by
computation that the pointwise first-return formula is correct for sampled
moduli.  This script records a finer diagnostic: along each first-return orbit
from the Theta seam, count which Lambda_E zero masks and stop ranks occur.

The main lesson from the first samples is that full zero-mask profiles are not
constant on the broad B20 source classes, while stop-rank count profiles are
much more stable.  That suggests the symbolic proof should track affine hit
times for the zero-mask predicates, not only the six return-time classes.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any

import verify_d5_even_routeE as route_e
import verify_d5_routeE_b20_branch as b20


def classify_source(m: int, a: int) -> str:
    h = m // 2
    r = b20.b20_counts(m)[0]
    if 1 <= a <= h - 2:
        return "L-ex" if a in {r, 2 * r} else "L-gen"
    if a == h - 1:
        return "F"
    if a == h:
        return "Mid"
    if h + 1 <= a <= m - 2:
        return "U-ex" if a in {h + r, h + 2 * r} else "U-gen"
    if a == m - 1:
        return "Last"
    raise ValueError((m, a))


def compact_counter(counter: Counter[int]) -> list[list[int]]:
    return [[int(key), int(value)] for key, value in sorted(counter.items())]


def trace_profile(m: int, a: int) -> dict[str, Any]:
    counts = b20.b20_counts(m)
    w = route_e.theta_state(m, 0, a)
    mask_counter: Counter[int] = Counter()
    stop_counter: Counter[int] = Counter()
    steps = 0
    while True:
        mask = route_e.shifted_zero_mask(w)
        stop = route_e.lam(route_e.PERT, mask, 0)
        mask_counter[mask] += 1
        stop_counter[stop] += 1
        steps += 1
        w = route_e.one_e_return_step_with_slot(m, 0, counts, w)
        target = route_e.theta_param(m, 0, w)
        if target is not None:
            return {
                "a": a,
                "class": classify_source(m, a),
                "dest": target,
                "steps": steps,
                "expected_steps": b20.expected_time_at(m, a),
                "stop_counter": compact_counter(stop_counter),
                "mask_counter": compact_counter(mask_counter),
            }
        if steps > m**4 + 5:
            raise RuntimeError(f"no B20 return for m={m}, a={a}")


def summarize_profiles(profiles: list[dict[str, Any]]) -> dict[str, Any]:
    by_class: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for profile in profiles:
        by_class[profile["class"]].append(profile)

    summary: dict[str, Any] = {}
    for name in sorted(by_class):
        rows = by_class[name]
        stop_profiles = Counter(
            tuple((key, value) for key, value in row["stop_counter"]) for row in rows
        )
        mask_profiles = Counter(
            tuple((key, value) for key, value in row["mask_counter"]) for row in rows
        )
        step_values = Counter(row["steps"] for row in rows)
        dest_deltas = Counter((row["dest"] - row["a"]) % row.get("m", 1) for row in rows)
        summary[name] = {
            "size": len(rows),
            "step_values": compact_counter(step_values),
            "distinct_stop_profiles": len(stop_profiles),
            "stop_profile_multiplicities": [
                {"multiplicity": count, "profile": [list(pair) for pair in profile]}
                for profile, count in stop_profiles.most_common()
            ],
            "distinct_mask_profiles": len(mask_profiles),
            "mask_profile_multiplicities": [
                {"multiplicity": count, "profile": [list(pair) for pair in profile]}
                for profile, count in mask_profiles.most_common(8)
            ],
            "mask_profile_multiplicity_tail": sum(
                count for _, count in mask_profiles.most_common()[8:]
            ),
            "dest_deltas": compact_counter(dest_deltas),
        }
    return summary


def analyze_modulus(m: int) -> dict[str, Any]:
    if m % 24 != 20:
        raise ValueError(f"B20 expects m == 20 mod 24, got {m}")
    profiles = [trace_profile(m, a) for a in range(1, m)]
    for profile in profiles:
        profile["m"] = m
    step_mismatches = [
        {
            "a": profile["a"],
            "got": profile["steps"],
            "expected": profile["expected_steps"],
        }
        for profile in profiles
        if profile["steps"] != profile["expected_steps"]
    ]
    return {
        "m": m,
        "q": b20.b20_q(m),
        "h": m // 2,
        "r": b20.b20_counts(m)[0],
        "counts": b20.b20_counts(m),
        "profile_summary": summarize_profiles(profiles),
        "step_formula_ok": not step_mismatches,
        "step_mismatches": step_mismatches[:10],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--moduli",
        default="20,44",
        help="comma-separated B20 moduli; 20,44 are fast enough for routine use",
    )
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()

    moduli = route_e.parse_moduli(args.moduli)
    results = [analyze_modulus(m) for m in moduli]
    payload = {
        "schema": "d5_routeE_b20_trace_profiles_v1",
        "moduli": moduli,
        "all_step_formulas_ok": all(result["step_formula_ok"] for result in results),
        "results": results,
    }

    for result in results:
        print(
            f"m={result['m']} q={result['q']} counts={result['counts']} "
            f"step_formula_ok={result['step_formula_ok']}"
        )
        for name, row in result["profile_summary"].items():
            stop_count = row["distinct_stop_profiles"]
            mask_count = row["distinct_mask_profiles"]
            steps = row["step_values"]
            print(
                f"  {name:5s} size={row['size']:2d} steps={steps} "
                f"stop_profiles={stop_count} mask_profiles={mask_count}"
            )

    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
        print(f"wrote {args.json_out}")

    if not payload["all_step_formulas_ok"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
