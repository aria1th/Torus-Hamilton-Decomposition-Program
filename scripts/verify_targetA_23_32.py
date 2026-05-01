#!/usr/bin/env python3
"""Concise verifier for the Target-A 23/32 section theorem candidate.

The post-update A5-to-A7 bundle isolates the following proof target for the
all-zero-set A5 base words ``23`` and ``32``:

* first return to Sigma has total excursion length m^4;
* the induced Sigma map is one cycle iff m != 2 mod 5;
* in the bad class m == 2 mod 5, the Sigma map has five cycles with explicit
  lengths;
* the return of the induced Sigma map to Sigma0 = {(a,0) : a != 0} is
  a -> a+1, with wrap m-1 -> 1.

This script checks exactly those finite claims without emitting the large
symbolic-table diagnostics from ``analyze_targetA_section.py``.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter
from pathlib import Path

from verify_4plus2_allN_bridge_cert import add_base_q, lambda1_direction


Word = tuple[int, ...]
Point = tuple[int, int]
State = tuple[int, int, int, int]


def parse_word(text: str) -> Word:
    if any(ch not in "01234" for ch in text):
        raise ValueError(f"word must use only A5 slots 0..4: {text}")
    return tuple(int(ch) for ch in text)


def word_string(word: Word) -> str:
    return "".join(str(slot) for slot in word)


def sigma_points(m: int) -> list[Point]:
    return [(a, b) for a in range(m) for b in range(m) if (a + b) % m != 0]


def state_from_sigma(point: Point, m: int) -> State:
    a, b = point
    # The hidden fifth coordinate is -a-b; only the first four coordinates are
    # stored by the bridge model.
    return (0, a % m, b % m, 0)


def sigma_from_state(state: State) -> Point:
    return (state[1], state[2])


def in_sigma(state: State, m: int) -> bool:
    return state[0] == 0 and state[3] == 0 and (state[1] + state[2]) % m != 0


def apply_word(state: State, word: Word, m: int) -> State:
    for slot in word:
        direction = lambda1_direction(state, slot, m)
        state = add_base_q(state, direction, m)
    return state


def first_return_table(word: Word, m: int) -> tuple[dict[Point, Point], dict[Point, int]]:
    table: dict[Point, Point] = {}
    lengths: dict[Point, int] = {}
    limit = m**4 + 1
    for point in sigma_points(m):
        state = state_from_sigma(point, m)
        for time in range(1, limit + 1):
            state = apply_word(state, word, m)
            if in_sigma(state, m):
                table[point] = sigma_from_state(state)
                lengths[point] = time
                break
        else:
            raise RuntimeError(
                f"no first return to Sigma for word={word_string(word)} m={m} point={point}"
            )
    return table, lengths


def cycle_lengths(table: dict[Point, Point]) -> list[int]:
    unseen = set(table)
    lengths = []
    while unseen:
        point = next(iter(unseen))
        length = 0
        while point in unseen:
            unseen.remove(point)
            length += 1
            point = table[point]
        lengths.append(length)
    return sorted(lengths)


def sigma0_return(table: dict[Point, Point], m: int) -> dict:
    failures = []
    steps = Counter()
    for a in range(1, m):
        point = (a, 0)
        seen: set[Point] = set()
        step_count = 0
        while True:
            if point in seen:
                failures.append({"from": a, "reason": "cycle before Sigma0 return"})
                break
            seen.add(point)
            point = table[point]
            step_count += 1
            if point[1] == 0:
                expected = a + 1
                if expected == m:
                    expected = 1
                if point != (expected, 0):
                    failures.append(
                        {
                            "from": a,
                            "to": list(point),
                            "expected": [expected, 0],
                            "steps": step_count,
                        }
                    )
                else:
                    steps[step_count] += 1
                break
    return {
        "ok": not failures,
        "failures": failures[:10],
        "return_step_counts": dict(sorted(steps.items())),
    }


def expected_bad_cycles(word: Word, m: int) -> list[int] | None:
    text = word_string(word)
    if m % 5 != 2:
        return None
    if text == "23":
        values = [
            (m * m + 9 * m - 2) // 5,
            (m * m - m + 3) // 5,
            (m * m - m - 2) // 5,
            (m * m - 6 * m + 3) // 5,
            (m * m - 6 * m - 2) // 5,
        ]
    elif text == "32":
        values = [
            (m * m + 9 * m - 12) // 5,
            (m * m - m + 8) // 5,
            (m * m - m - 2) // 5,
            (m * m - 6 * m + 3) // 5,
            (m * m - 6 * m + 3) // 5,
        ]
    else:
        return None
    return sorted(values)


def analyze(word: Word, m: int) -> dict:
    table, lengths = first_return_table(word, m)
    cycles = cycle_lengths(table)
    expected_cycles = expected_bad_cycles(word, m)
    one_cycle_expected = m % 5 != 2
    return {
        "m": m,
        "word": word_string(word),
        "sigma_size": m * (m - 1),
        "section_cycle_lengths": cycles,
        "section_single_cycle": cycles == [m * (m - 1)],
        "section_single_cycle_expected": one_cycle_expected,
        "section_single_cycle_ok": (cycles == [m * (m - 1)]) == one_cycle_expected,
        "return_time_sum": sum(lengths.values()),
        "return_time_sum_ok": sum(lengths.values()) == m**4,
        "return_time_distribution_sample": dict(Counter(lengths.values()).most_common(12)),
        "sigma0_return": sigma0_return(table, m),
        "expected_bad_cycle_lengths": expected_cycles,
        "bad_cycle_formula_ok": expected_cycles is None or cycles == expected_cycles,
    }


def parse_moduli(text: str) -> list[int]:
    moduli = [int(part) for part in text.split(",") if part.strip()]
    bad = [m for m in moduli if m < 5 or m % 2 == 0]
    if bad:
        raise ValueError(f"Target-A 23/32 verifier expects odd m >= 5, got {bad}")
    return moduli


def default_moduli() -> list[int]:
    return [5, 7, 9, 11, 13, 17, 27, 37, 47]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--moduli", default=",".join(str(m) for m in default_moduli()))
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
            result["section_single_cycle_ok"]
            and result["return_time_sum_ok"]
            and result["sigma0_return"]["ok"]
            and result["bad_cycle_formula_ok"]
            for result in results
        ),
        "results": results,
    }

    for result in results:
        print(
            "m={m} word={word} cycles={section_cycle_lengths} "
            "single_ok={section_single_cycle_ok} sum_ok={return_time_sum_ok} "
            "sigma0_ok={sigma0_ok} bad_formula_ok={bad_cycle_formula_ok}".format(
                sigma0_ok=result["sigma0_return"]["ok"], **result
            )
        )
    print(f"all_ok={payload['all_ok']}")

    if args.json_out:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
        print(f"wrote {args.json_out}")


if __name__ == "__main__":
    main()
