#!/usr/bin/env python3
"""Verifier for the Target-A 23/32 seam quotient.

The current A5-to-A7 proof bundle reduces the generic ``23/32`` primitive
block to a seam quotient on

    Q = {B_i=(i,0)} union {A_j=(0,j)}.

For odd ``m = 2h + 1`` and ``m >= 13``, the first-return map to ``Q`` has a
common B-chain and a collapsed one-dimensional quotient ``phi_h`` on
``{1,...,h}``.  This script checks:

* the arithmetic cycle theorem for ``phi_h``;
* finite Q-hitting for the Sigma first-return map;
* the stated Q-first-return table for words ``23`` and ``32``.

It is an audit artifact for the symbolic proof target, not a replacement for
the eventual Lean theorem.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from verify_targetA_23_32 import (
    Point,
    Word,
    first_return_table,
    parse_moduli,
    parse_word,
    word_string,
)

Label = tuple[str, int]


def rep_1_to_h(value: int, h: int) -> int:
    return ((value - 1) % h) + 1


def phi_h(h: int, x: int) -> int:
    if not 1 <= x <= h:
        raise ValueError((h, x))
    if x <= 3:
        return rep_1_to_h(x - 3, h)
    if x <= 5:
        return rep_1_to_h(x - 8, h)
    return rep_1_to_h(x - 5, h)


def phi_cycle_lengths(h: int) -> list[int]:
    unseen = set(range(1, h + 1))
    lengths = []
    while unseen:
        x = min(unseen)
        length = 0
        while x in unseen:
            unseen.remove(x)
            length += 1
            x = phi_h(h, x)
        lengths.append(length)
    return sorted(lengths)


def expected_phi_cycle_lengths(h: int) -> list[int]:
    if h % 5 != 3:
        return [h]
    large = (h + 4) // 5
    small = h // 5
    return sorted([large, large, large, small, small])


def analyze_phi(max_h: int) -> dict:
    rows = []
    for h in range(6, max_h + 1):
        cycles = phi_cycle_lengths(h)
        expected = expected_phi_cycle_lengths(h)
        rows.append(
            {
                "h": h,
                "h_mod_5": h % 5,
                "m": 2 * h + 1,
                "cycles": cycles,
                "expected_cycles": expected,
                "ok": cycles == expected,
            }
        )
    return {
        "h_range": [6, max_h],
        "all_ok": all(row["ok"] for row in rows),
        "rows": rows,
    }


def q_label(point: Point) -> Label | None:
    a, b = point
    if b == 0 and a != 0:
        return ("B", a)
    if a == 0 and b != 0:
        return ("A", b)
    return None


def q_point(label: Label) -> Point:
    kind, value = label
    if kind == "B":
        return (value, 0)
    if kind == "A":
        return (0, value)
    raise ValueError(label)


def label_to_json(label: Label) -> list[object]:
    return [label[0], label[1]]


def q_labels(m: int) -> list[Label]:
    return [("B", i) for i in range(1, m)] + [("A", i) for i in range(1, m)]


def q_hitting(table: dict[Point, Point], m: int) -> dict:
    failures = []
    hit_steps = []
    limit = len(table) + 1
    for start in table:
        point = start
        for steps in range(limit + 1):
            label = q_label(point)
            if label is not None:
                hit_steps.append(steps)
                break
            point = table[point]
        else:
            failures.append(list(start))
            if len(failures) >= 10:
                break
    return {
        "ok": not failures,
        "max_steps": max(hit_steps) if hit_steps else None,
        "zero_step_hits": sum(1 for steps in hit_steps if steps == 0),
        "failures": failures,
    }


def q_first_return(table: dict[Point, Point], m: int) -> dict[Label, tuple[Label, int]]:
    out: dict[Label, tuple[Label, int]] = {}
    limit = len(table) + 1
    for label in q_labels(m):
        point = q_point(label)
        for steps in range(1, limit + 1):
            point = table[point]
            target = q_label(point)
            if target is not None:
                out[label] = (target, steps)
                break
        else:
            raise RuntimeError(f"no Q return for m={m} label={label}")
    return out


def tau23(h: int, x: int) -> int:
    if 1 <= x <= 3:
        return rep_1_to_h(x + h - 4, h)
    if 4 <= x <= 5:
        return rep_1_to_h(x + h - 9, h)
    if x == 6:
        return rep_1_to_h(x + h - 6, h)
    if 7 <= x <= h:
        return x - 6
    raise ValueError((h, x))


def expected_q_target(word: Word, m: int, label: Label) -> Label:
    text = word_string(word)
    h = (m - 1) // 2
    kind, value = label
    if kind == "B":
        if value < m - 1:
            return ("B", value + 1)
        return ("A", 1)

    if kind != "A":
        raise ValueError(label)

    if text == "23":
        if value % 2 == 0:
            x = value // 2
            if x <= h - 1:
                return ("A", 2 * x + 1)
            return ("B", 1)
        x = (value + 1) // 2
        return ("A", 2 * tau23(h, x))

    if text == "32":
        if value % 2 == 1:
            x = (value + 1) // 2
            return ("A", 2 * x)
        x = value // 2
        if x == 6:
            return ("B", 1)
        return ("A", 2 * phi_h(h, x) - 1)

    raise ValueError(text)


def analyze_q_table(word: Word, m: int) -> dict:
    if m < 13 or m % 2 == 0:
        raise ValueError(f"Q seam quotient formula expects odd m >= 13, got {m}")
    table, lengths = first_return_table(word, m)
    q_return = q_first_return(table, m)
    mismatches = []
    for label in q_labels(m):
        got, steps = q_return[label]
        expected = expected_q_target(word, m, label)
        if got != expected:
            mismatches.append(
                {
                    "from": label_to_json(label),
                    "got": label_to_json(got),
                    "expected": label_to_json(expected),
                    "q_return_steps": steps,
                }
            )
            if len(mismatches) >= 10:
                break

    h = (m - 1) // 2
    phi_cycles = phi_cycle_lengths(h)
    return {
        "m": m,
        "h": h,
        "word": word_string(word),
        "q_hitting": q_hitting(table, m),
        "q_formula_ok": not mismatches,
        "q_formula_mismatches": mismatches,
        "return_time_sum": sum(lengths.values()),
        "return_time_sum_ok": sum(lengths.values()) == m**4,
        "phi_cycles": phi_cycles,
        "phi_expected_cycles": expected_phi_cycle_lengths(h),
        "phi_cycle_ok": phi_cycles == expected_phi_cycle_lengths(h),
        "primitive_quotient_expected": h % 5 != 3,
        "m_mod_5": m % 5,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--moduli", default="13,17,19,27,37")
    parser.add_argument("--words", default="23,32")
    parser.add_argument("--phi-max", type=int, default=80)
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()

    moduli = parse_moduli(args.moduli)
    words = [parse_word(word.strip()) for word in args.words.split(",") if word.strip()]
    phi = analyze_phi(args.phi_max)
    q_results = [analyze_q_table(word, m) for m in moduli for word in words]
    payload = {
        "moduli": moduli,
        "words": [word_string(word) for word in words],
        "phi": phi,
        "q_results": q_results,
        "all_ok": phi["all_ok"]
        and all(
            result["q_hitting"]["ok"]
            and result["q_formula_ok"]
            and result["return_time_sum_ok"]
            and result["phi_cycle_ok"]
            for result in q_results
        ),
    }

    print(f"phi_all_ok={phi['all_ok']} h_range={phi['h_range']}")
    for result in q_results:
        print(
            "m={m} word={word} q_hit_ok={q_hit_ok} q_formula_ok={q_formula_ok} "
            "sum_ok={return_time_sum_ok} phi_cycles={phi_cycles} "
            "primitive_expected={primitive_quotient_expected}".format(
                q_hit_ok=result["q_hitting"]["ok"], **result
            )
        )
    print(f"all_ok={payload['all_ok']}")

    if args.json_out:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
        print(f"wrote {args.json_out}")


if __name__ == "__main__":
    main()
