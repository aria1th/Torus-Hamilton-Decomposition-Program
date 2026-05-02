#!/usr/bin/env python3
"""Verify the D5 even Route-E B20 branch candidate.

B20 is the branch ``m = 24*q + 20`` with slot zero and counts

    nu = (r, 0, 0, h+r, r),  h = m/2, r = (h-1)/3.

The expected first return on the Theta seam is the two-block map

    1 <= a <= h-2:   a |-> a + h + 1
    h-1 <= a <= m-1: a |-> a + h + 2

modulo ``m``.  This script checks that finite claim using the repo Route-E
small-seam verifier.  It also checks the fitted six-value return-time
distribution and pointwise return-time partition.  It is a regression
artifact, not the symbolic proof.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter
from pathlib import Path

import verify_d5_even_routeE as route_e


def b20_counts(m: int) -> tuple[int, int, int, int, int]:
    if m % 24 != 20:
        raise ValueError(f"B20 expects m == 20 mod 24, got {m}")
    h = m // 2
    r = (h - 1) // 3
    if 3 * r != h - 1:
        raise ValueError(f"B20 r is not integral for m={m}")
    return (r, 0, 0, h + r, r)


def expected_blocks(m: int) -> list[dict]:
    h = m // 2
    return [
        {"start": 1, "end": h - 2, "delta": h + 1, "length": h - 2},
        {"start": h - 1, "end": m - 1, "delta": h + 2, "length": h + 1},
    ]


def b20_q(m: int) -> int:
    if (m - 20) % 24 != 0:
        raise ValueError(f"B20 expects m = 24*q+20, got {m}")
    return (m - 20) // 24


def expected_time_distribution(m: int) -> dict[int, int]:
    """Return the fitted B20 return-time distribution.

    The six time values are written as polynomials in q where m = 24*q + 20.
    This is proof-target data extracted from the verified B20 instances.
    """
    q = b20_q(m)
    h = m // 2
    a = 13824 * q**3 + 34272 * q**2 + 28320 * q + 7806
    c = a + m * (m + 1)
    e = 20736 * q**3 + 50976 * q**2 + 41772 * q + 11416
    f = 20736 * q**3 + 51552 * q**2 + 42780 * q + 11862
    return {
        a: 2,
        a + m: h - 4,
        c: 3,
        c + m: h - 4,
        e: 1,
        f: 1,
    }


def b20_time_values(m: int) -> dict[str, int]:
    q = b20_q(m)
    a_time = 13824 * q**3 + 34272 * q**2 + 28320 * q + 7806
    c_time = a_time + m * (m + 1)
    e_time = 20736 * q**3 + 50976 * q**2 + 41772 * q + 11416
    f_time = 20736 * q**3 + 51552 * q**2 + 42780 * q + 11862
    return {
        "A": a_time,
        "B": a_time + m,
        "C": c_time,
        "D": c_time + m,
        "E": e_time,
        "F": f_time,
    }


def expected_time_at(m: int, a: int) -> int:
    h = m // 2
    r = b20_counts(m)[0]
    values = b20_time_values(m)
    if 1 <= a <= h - 2:
        return values["C"] if a in {r, 2 * r} else values["D"]
    if a == h - 1:
        return values["F"]
    if a == h:
        return values["C"]
    if h + 1 <= a <= m - 2:
        return values["A"] if a in {h + r, h + 2 * r} else values["B"]
    if a == m - 1:
        return values["E"]
    raise ValueError((m, a))


def time_runs(times: dict[int, int]) -> list[dict]:
    runs = []
    start = 1
    previous = 1
    current = times[1]
    for a in range(2, len(times) + 1):
        value = times[a]
        if value != current:
            runs.append(
                {
                    "start": start,
                    "end": previous,
                    "time": current,
                    "length": previous - start + 1,
                }
            )
            start = a
            current = value
        previous = a
    runs.append(
        {
            "start": start,
            "end": previous,
            "time": current,
            "length": previous - start + 1,
        }
    )
    return runs


def first_return_data(m: int, counts: tuple[int, int, int, int, int]) -> dict:
    seam_port = 2
    first_return = {}
    return_times = {}
    start_ok = True
    no_return = []
    for a in range(1, m):
        w = route_e.theta_state(m, 0, a)
        if route_e.lam(route_e.PERT, route_e.shifted_zero_mask(w), 0) != seam_port:
            start_ok = False
        for time in range(1, m**4 + 6):
            w = route_e.one_e_return_step_with_slot(m, 0, counts, w)
            b = route_e.theta_param(m, 0, w)
            if b is not None:
                first_return[a] = b
                return_times[a] = time
                break
        else:
            no_return.append(a)
            break

    cycle_lengths = (
        route_e.cycle_lengths_from_param_map(first_return, range(1, m))
        if not no_return
        else []
    )
    blocks = route_e.translation_blocks(m, first_return) if not no_return else []
    return_time_sum = sum(return_times.values())
    return {
        "start_ok": start_ok,
        "no_return_examples": no_return,
        "first_return": first_return,
        "return_times": return_times,
        "cycle_lengths": cycle_lengths,
        "return_time_sum": return_time_sum,
        "expected_return_time_sum": m**4,
        "translation_blocks": blocks,
        "time_distribution": dict(sorted(Counter(return_times.values()).items())),
        "ok": (
            start_ok
            and not no_return
            and cycle_lengths == [m - 1]
            and return_time_sum == m**4
        ),
    }


def weighted_time_sum(distribution: dict[int, int]) -> int:
    return sum(time * count for time, count in distribution.items())


def analyze_modulus(m: int) -> dict:
    counts = b20_counts(m)
    result = first_return_data(m, counts)
    expected = expected_blocks(m)
    expected_distribution = expected_time_distribution(m)
    expected_times = {a: expected_time_at(m, a) for a in range(1, m)}
    time_mismatches = [
        {
            "a": a,
            "got": result["return_times"].get(a),
            "expected": expected_times[a],
        }
        for a in range(1, m)
        if result["return_times"].get(a) != expected_times[a]
    ]
    return {
        "m": m,
        "h": m // 2,
        "q": b20_q(m),
        "r": counts[0],
        "slot": 0,
        "counts": counts,
        "small_seam_ok": result["ok"],
        "cycle_lengths": result["cycle_lengths"],
        "return_time_sum": result["return_time_sum"],
        "expected_return_time_sum": result["expected_return_time_sum"],
        "return_time_sum_ok": result["return_time_sum"] == m**4,
        "translation_blocks": result["translation_blocks"],
        "expected_translation_blocks": expected,
        "translation_blocks_ok": result["translation_blocks"] == expected,
        "time_distribution": result["time_distribution"],
        "expected_time_distribution": expected_distribution,
        "time_distribution_ok": result["time_distribution"] == expected_distribution,
        "return_time_runs": time_runs(result["return_times"])
        if not result["no_return_examples"]
        else [],
        "expected_return_time_runs": time_runs(expected_times),
        "return_time_formula_ok": not time_mismatches,
        "return_time_formula_mismatches": time_mismatches[:10],
        "expected_distribution_sum": weighted_time_sum(expected_distribution),
        "expected_distribution_sum_ok": weighted_time_sum(expected_distribution) == m**4,
        "ok": (
            result["ok"]
            and result["translation_blocks"] == expected
            and result["time_distribution"] == expected_distribution
            and not time_mismatches
            and weighted_time_sum(expected_distribution) == m**4
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--moduli",
        default="20,44",
        help="comma-separated B20 moduli; larger cases such as 68,92 are slower",
    )
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()

    moduli = route_e.parse_moduli(args.moduli)
    results = [analyze_modulus(m) for m in moduli]
    payload = {
        "schema": "d5_routeE_b20_branch_v1",
        "moduli": moduli,
        "all_ok": all(result["ok"] for result in results),
        "results": results,
    }

    for result in results:
        print(
            "m={m} counts={counts} small_ok={small_seam_ok} "
            "blocks_ok={translation_blocks_ok} times_ok={time_distribution_ok} "
            "time_formula_ok={return_time_formula_ok} sum_ok={return_time_sum_ok} "
            "blocks={translation_blocks}".format(**result)
        )
    print(f"all_ok={payload['all_ok']}")

    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
        print(f"wrote {args.json_out}")
    if not payload["all_ok"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
