#!/usr/bin/env python3
"""Verify the Target-A exceptional 00 phase-splice table.

This is a finite regression for the reduced exceptional A5 base problem in the
class ``m = 10*t + 7``.  It checks the phase table for the correction block
``00`` on the five seam lanes of the ``23/32`` quotient.

The script is an audit artifact for the symbolic proof target.  It does not
choose the final correction schedule or prove the all-odd Target-A theorem.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from verify_targetA_23_32 import (
    Word,
    apply_word,
    in_sigma,
    parse_moduli,
    parse_word,
    sigma_from_state,
    state_from_sigma,
    word_string,
)
from verify_targetA_23_32_seam_quotient import Label, q_label

Lane = tuple[int, int]


def lane_lists(t: int) -> dict[int, list[int]]:
    lanes: dict[int, list[int]] = {}
    for residue in (1, 2, 3):
        lanes[residue] = [residue] + [
            5 * (t - phase + 1) + residue for phase in range(1, t + 1)
        ]
    lanes[4] = [4] + [5 * (t - phase) + 4 for phase in range(1, t)]
    lanes[0] = [5] + [5 * (t - phase + 1) for phase in range(1, t)]
    return lanes


def lane_positions(t: int) -> dict[int, Lane]:
    positions = {}
    for residue, lane in lane_lists(t).items():
        for phase, x in enumerate(lane):
            positions[x] = (residue, phase)
    return positions


def expected_correction_target(word: Word, t: int, lane: Lane) -> Lane:
    residue, phase = lane
    if residue == 1:
        return (2, phase)
    if residue == 2:
        return (3, phase)
    if residue == 4:
        return (0, phase)
    if residue == 0:
        return (1, t if phase == 0 else phase)
    if residue == 3:
        if phase == 0:
            return (4, 0)
        if phase == 1:
            if word_string(word) == "23":
                return (1, 0)
            if word_string(word) == "32":
                return (2, 1)
            raise ValueError(word)
        return (4, phase - 1)
    raise ValueError(lane)


def first_q_after_state(state, word: Word, m: int) -> tuple[Label, int]:
    current = state
    for extra in range(1, m**4 + 11):
        current = apply_word(current, word, m)
        if in_sigma(current, m):
            label = q_label(sigma_from_state(current))
            if label is not None:
                return label, extra
    raise RuntimeError(f"no Q return after state for m={m} word={word_string(word)}")


def actual_correction_target(m: int, h: int, word: Word, x: int) -> tuple[int, int]:
    a_label = (2 * x - 1) % m
    state = state_from_sigma((0, a_label), m)
    after_c = apply_word(state, (0, 0), m)
    if in_sigma(after_c, m):
        label = q_label(sigma_from_state(after_c))
        if label is not None and label[0] == "A":
            return (label[1] + 1) // 2, 0
    label, extra = first_q_after_state(after_c, word, m)
    if label[0] != "A":
        raise RuntimeError(
            f"correction target is not an A-label: m={m} word={word_string(word)} x={x}"
        )
    return (label[1] + 1) // 2, extra


def analyze_word(m: int, word: Word) -> dict:
    if m < 17 or m % 10 != 7:
        raise ValueError(
            f"expected exceptional modulus m = 10*t+7 with t >= 1, got {m}"
        )
    h = (m - 1) // 2
    t = (h - 3) // 5
    positions = lane_positions(t)
    rows = []
    mismatches = []
    for x in range(1, h + 1):
        source = positions[x]
        actual_x, extra_h = actual_correction_target(m, h, word, x)
        actual_lane = positions[actual_x]
        expected_lane = expected_correction_target(word, t, source)
        row = {
            "x": x,
            "source": list(source),
            "actual_x": actual_x,
            "actual": list(actual_lane),
            "expected": list(expected_lane),
            "extra_H_returns": extra_h,
            "ok": actual_lane == expected_lane,
        }
        rows.append(row)
        if not row["ok"]:
            mismatches.append(row)
    return {
        "m": m,
        "h": h,
        "t": t,
        "word": word_string(word),
        "lanes": {str(residue): lane for residue, lane in lane_lists(t).items()},
        "ok": not mismatches,
        "mismatches": mismatches[:10],
        "boundary_extra_H_returns": [
            row for row in rows if row["extra_H_returns"] != 0
        ],
        "rows": rows,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--moduli", default="17,27,37")
    parser.add_argument("--words", default="23,32")
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()

    moduli = parse_moduli(args.moduli)
    words = [parse_word(word.strip()) for word in args.words.split(",") if word.strip()]
    results = [analyze_word(m, word) for m in moduli for word in words]
    payload = {
        "schema": "d7_targetA_exceptional_phase_splice_v1",
        "moduli": moduli,
        "words": [word_string(word) for word in words],
        "all_ok": all(result["ok"] for result in results),
        "results": results,
    }

    for result in results:
        print(
            "m={m} word={word} ok={ok} boundary_extra={boundary}".format(
                boundary=[
                    {
                        "x": row["x"],
                        "source": row["source"],
                        "actual": row["actual"],
                        "extra": row["extra_H_returns"],
                    }
                    for row in result["boundary_extra_H_returns"]
                ],
                **result,
            )
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
