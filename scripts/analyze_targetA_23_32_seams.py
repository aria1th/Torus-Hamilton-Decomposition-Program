#!/usr/bin/env python3
"""Analyze the Sigma0 seam decomposition for Target-A words 23 and 32.

``verify_targetA_23_32.py`` checks the finite theorem-candidate gates.  This
script records the seam shape behind those gates:

* in the good class, every Sigma point lies in the Sigma0 component;
* in the bad class m == 2 mod 5, exactly one cycle meets Sigma0 and the four
  remaining cycles avoid Sigma0 with the predicted lengths.

The output is meant to guide the eventual symbolic proof of seam connectivity
and the bad-class correction-row construction.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter
from pathlib import Path

from verify_targetA_23_32 import (
    Point,
    Word,
    first_return_table,
    parse_moduli,
    parse_word,
    word_string,
)


def decompose_cycles(table: dict[Point, Point]) -> list[list[Point]]:
    unseen = set(table)
    cycles = []
    while unseen:
        start = min(unseen)
        point = start
        cycle = []
        while point in unseen:
            unseen.remove(point)
            cycle.append(point)
            point = table[point]
        cycles.append(cycle)
    return sorted(cycles, key=lambda cycle: (not meets_sigma0(cycle), len(cycle), cycle[0]))


def meets_sigma0(cycle: list[Point]) -> bool:
    return any(b == 0 for _a, b in cycle)


def bad_cycle_terms(word: Word, m: int) -> dict[str, int] | None:
    if m % 5 != 2:
        return None
    text = word_string(word)
    if text == "23":
        return {
            "sigma0": (m * m + 9 * m - 2) // 5,
            "off_a": (m * m - m + 3) // 5,
            "off_b": (m * m - m - 2) // 5,
            "off_c": (m * m - 6 * m + 3) // 5,
            "off_d": (m * m - 6 * m - 2) // 5,
        }
    if text == "32":
        return {
            "sigma0": (m * m + 9 * m - 12) // 5,
            "off_a": (m * m - m + 8) // 5,
            "off_b": (m * m - m - 2) // 5,
            "off_c": (m * m - 6 * m + 3) // 5,
            "off_d": (m * m - 6 * m + 3) // 5,
        }
    return None


def residue_histogram(cycle: list[Point], m: int, modulus: int = 5) -> dict[str, dict[str, int]]:
    if m % modulus != 2:
        return {}
    features = {
        "a": lambda a, b: a,
        "b": lambda a, b: b,
        "sum": lambda a, b: a + b,
        "a_minus_b": lambda a, b: a - b,
    }
    out = {}
    for name, fn in features.items():
        counts = Counter(str(fn(a, b) % modulus) for a, b in cycle)
        out[name] = dict(sorted(counts.items(), key=lambda item: int(item[0])))
    return out


def cycle_summary(cycle: list[Point], m: int) -> dict:
    sigma0_as = [a for a, b in cycle if b == 0]
    return {
        "length": len(cycle),
        "meets_sigma0": bool(sigma0_as),
        "sigma0_count": len(sigma0_as),
        "sigma0_a_sample": sigma0_as[:12],
        "sample_points": [list(point) for point in cycle[:12]],
        "boundary_counts": {
            "a_zero": sum(1 for a, _b in cycle if a == 0),
            "b_zero": len(sigma0_as),
        },
        "mod5_histograms": residue_histogram(cycle, m),
    }


def analyze(word: Word, m: int) -> dict:
    table, lengths = first_return_table(word, m)
    cycles = decompose_cycles(table)
    sigma0_cycles = [cycle for cycle in cycles if meets_sigma0(cycle)]
    off_cycles = [cycle for cycle in cycles if not meets_sigma0(cycle)]
    terms = bad_cycle_terms(word, m)
    sigma_size = m * (m - 1)
    good_class = m % 5 != 2
    good_connectivity_ok = (
        good_class
        and len(cycles) == 1
        and len(sigma0_cycles) == 1
        and len(sigma0_cycles[0]) == sigma_size
    )
    bad_decomposition_ok = False
    if terms is not None and len(sigma0_cycles) == 1:
        bad_decomposition_ok = (
            len(sigma0_cycles[0]) == terms["sigma0"]
            and sorted(len(cycle) for cycle in off_cycles)
            == sorted(value for key, value in terms.items() if key != "sigma0")
        )

    return {
        "m": m,
        "word": word_string(word),
        "sigma_size": sigma_size,
        "cycle_lengths": sorted(len(cycle) for cycle in cycles),
        "return_time_sum": sum(lengths.values()),
        "return_time_sum_ok": sum(lengths.values()) == m**4,
        "sigma0_cycle_count": len(sigma0_cycles),
        "sigma0_cycle_lengths": sorted(len(cycle) for cycle in sigma0_cycles),
        "off_sigma0_cycle_lengths": sorted(len(cycle) for cycle in off_cycles),
        "points_reaching_sigma0": sum(len(cycle) for cycle in sigma0_cycles),
        "bad_cycle_terms": terms,
        "good_connectivity_ok": good_connectivity_ok if good_class else None,
        "bad_decomposition_ok": bad_decomposition_ok if terms is not None else None,
        "cycles": [cycle_summary(cycle, m) for cycle in cycles],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--moduli", default="7,9,17,27,37,47")
    parser.add_argument("--words", default="23,32")
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()

    moduli = parse_moduli(args.moduli)
    words = [parse_word(word.strip()) for word in args.words.split(",") if word.strip()]
    results = [analyze(word, m) for m in moduli for word in words]
    payload = {
        "moduli": moduli,
        "words": [word_string(word) for word in words],
        "all_ok": all(
            result["return_time_sum_ok"]
            and (
                result["good_connectivity_ok"] is True
                or result["bad_decomposition_ok"] is True
            )
            for result in results
        ),
        "results": results,
    }

    for result in results:
        if result["bad_decomposition_ok"] is None:
            gate = f"good_connectivity_ok={result['good_connectivity_ok']}"
        else:
            gate = f"bad_decomposition_ok={result['bad_decomposition_ok']}"
        print(
            "m={m} word={word} sigma0_lengths={sigma0_cycle_lengths} "
            "off_lengths={off_sigma0_cycle_lengths} points_to_sigma0={points_reaching_sigma0} "
            "sum_ok={return_time_sum_ok} {gate}".format(gate=gate, **result)
        )
    print(f"all_ok={payload['all_ok']}")

    if args.json_out:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
        print(f"wrote {args.json_out}")


if __name__ == "__main__":
    main()
