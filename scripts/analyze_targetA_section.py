#!/usr/bin/env python3
"""Section-return analyzer for the D7 odd Target-A base problem.

Target A asks for all-zero-set A5 base words whose return map is a single
cycle of length m^4.  The intended proof interface is stronger than a black-box
finite cycle check: prove primitiveity by first return to

    Sigma = {(0,a,b,0,-a-b) : a+b != 0}.

This script audits candidate base words against that interface.  It reports
finite primitiveity, first-return data on Sigma, total excursion length, and
coarse purity diagnostics for possible symbolic first-return tables.
"""
from __future__ import annotations

import argparse
import json
from collections import Counter, defaultdict
from pathlib import Path
from typing import Callable

from verify_4plus2_allN_bridge_cert import BridgeModel, base_index, base_tuple
from analyze_4plus2_base_rows import base_step_for_word, parse_word, word_string


def cycle_lengths(size: int, step: Callable[[int], int]) -> list[int]:
    seen = bytearray(size)
    lengths = []
    for start in range(size):
        if seen[start]:
            continue
        state = start
        length = 0
        while not seen[state]:
            seen[state] = 1
            length += 1
            state = step(state)
        lengths.append(length)
    return sorted(lengths)


def is_sigma_tuple(xs: tuple[int, int, int, int], m: int) -> bool:
    return xs[0] == 0 and xs[3] == 0 and (xs[1] + xs[2]) % m != 0


def sigma_params(m: int) -> list[tuple[int, int, int]]:
    out = []
    for a in range(m):
        for b in range(m):
            if (a + b) % m != 0:
                out.append((base_index((0, a, b, 0), m), a, b))
    return out


def first_return_records(
    model: BridgeModel, word: tuple[int, ...], max_steps: int | None = None
) -> tuple[list[dict], list[dict]]:
    m = model.m
    limit = max_steps or m**4
    step = lambda state: base_step_for_word(model, word, state)
    records = []
    failures = []
    for state, a, b in sigma_params(m):
        x = step(state)
        time = 1
        while not is_sigma_tuple(base_tuple(x, m), m):
            x = step(x)
            time += 1
            if time > limit:
                failures.append({"from": [a, b], "reason": "no return within limit"})
                break
        if time > limit:
            continue
        y = base_tuple(x, m)
        a2, b2 = y[1], y[2]
        records.append(
            {
                "from": [a, b],
                "to": [a2, b2],
                "delta": [(a2 - a) % m, (b2 - b) % m],
                "sum": (a + b) % m,
                "target_sum": (a2 + b2) % m,
                "time": time,
            }
        )
    return records, failures


def section_cycle_lengths(m: int, records: list[dict]) -> list[int]:
    sigma = [(a, b) for _state, a, b in sigma_params(m)]
    index = {ab: i for i, ab in enumerate(sigma)}
    perm = [0] * len(sigma)
    for rec in records:
        src = tuple(rec["from"])
        dst = tuple(rec["to"])
        if src not in index or dst not in index:
            raise ValueError((src, dst))
        perm[index[src]] = index[dst]
    seen = bytearray(len(perm))
    lengths = []
    for start in range(len(perm)):
        if seen[start]:
            continue
        x = start
        length = 0
        while not seen[x]:
            seen[x] = 1
            length += 1
            x = perm[x]
        lengths.append(length)
    return sorted(lengths)


def segment_coverage(model: BridgeModel, word: tuple[int, ...], records: list[dict]) -> dict:
    m = model.m
    step = lambda state: base_step_for_word(model, word, state)
    visited = bytearray(m**4)
    duplicate_hits = 0
    visits = 0
    for rec in records:
        a, b = rec["from"]
        state = base_index((0, a, b, 0), m)
        for _ in range(rec["time"]):
            if visited[state]:
                duplicate_hits += 1
            visited[state] = 1
            visits += 1
            state = step(state)
    return {
        "segment_visits": visits,
        "unique_segment_states": sum(visited),
        "duplicate_segment_hits": duplicate_hits,
        "covers_all_states_once": visits == m**4 and sum(visited) == m**4 and duplicate_hits == 0,
    }


def signature(record: dict) -> tuple[int, int, int, int]:
    da, db = record["delta"]
    return (da, db, record["target_sum"], record["time"])


def boundary_class(value: int, m: int) -> str:
    if value == 0:
        return "0"
    if value == 1 % m:
        return "1"
    if value == (m - 1) % m:
        return "-1"
    return "other"


def partition_summaries(m: int, records: list[dict]) -> dict:
    features: dict[str, Callable[[dict], object]] = {
        "sum": lambda r: r["sum"],
        "b": lambda r: r["from"][1],
        "sum_b": lambda r: (r["sum"], r["from"][1]),
        "sum_b_boundary": lambda r: (r["sum"], boundary_class(r["from"][1], m)),
        "sum_a_boundary_b_boundary": lambda r: (
            r["sum"],
            boundary_class(r["from"][0], m),
            boundary_class(r["from"][1], m),
        ),
        "source_zero_mask": lambda r: (
            r["from"][0] == 0,
            r["from"][1] == 0,
            (r["sum"] == 0),
        ),
    }
    out = {}
    for name, key_fn in features.items():
        groups: dict[str, Counter] = defaultdict(Counter)
        for rec in records:
            groups[json.dumps(key_fn(rec), sort_keys=True)][signature(rec)] += 1
        pure = sum(1 for counter in groups.values() if len(counter) == 1)
        total = len(groups)
        majority = sum(counter.most_common(1)[0][1] for counter in groups.values())
        ambiguous = []
        for key, counter in groups.items():
            if len(counter) <= 1:
                continue
            ambiguous.append(
                {
                    "key": json.loads(key),
                    "variants": [
                        {"signature": list(sig), "count": count}
                        for sig, count in counter.most_common(4)
                    ],
                }
            )
            if len(ambiguous) >= 5:
                break
        out[name] = {
            "pure_classes": pure,
            "classes": total,
            "majority_fraction": majority / len(records) if records else 0.0,
            "ambiguous_examples": ambiguous,
        }
    return out


def analyze_word(m: int, word: tuple[int, ...], include_records: bool) -> dict:
    model = BridgeModel(m)
    step = lambda state: base_step_for_word(model, word, state)
    lengths = cycle_lengths(m**4, step)
    records, failures = first_return_records(model, word)
    section_lengths = [] if failures else section_cycle_lengths(m, records)
    result = {
        "m": m,
        "word": word_string(word),
        "length": len(word),
        "base_cycle_lengths": lengths,
        "base_single_cycle": lengths == [m**4],
        "sigma_size": len(sigma_params(m)),
        "first_return_failures": failures[:10],
        "section_cycle_lengths": section_lengths,
        "section_single_cycle": section_lengths == [len(sigma_params(m))],
        "return_time_sum": sum(rec["time"] for rec in records),
        "return_time_distribution": dict(sorted(Counter(rec["time"] for rec in records).items())),
        "segment_coverage": segment_coverage(model, word, records) if not failures else None,
        "partition_summaries": partition_summaries(m, records) if records else {},
        "samples": records[: min(20, len(records))],
    }
    if include_records:
        result["records"] = records
    return result


def parse_moduli(value: str) -> list[int]:
    return [int(part) for part in value.split(",") if part.strip()]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--moduli", default="5,7,9,11,13,15,17")
    parser.add_argument("--words", default="332,01302,4204204")
    parser.add_argument("--include-records", action="store_true")
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()

    payload = {
        "moduli": parse_moduli(args.moduli),
        "words": [word.strip() for word in args.words.split(",") if word.strip()],
        "analyses": [],
    }
    for m in payload["moduli"]:
        for word_text in payload["words"]:
            payload["analyses"].append(
                analyze_word(m, parse_word(word_text), args.include_records)
            )

    text = json.dumps(payload, indent=2, sort_keys=True)
    if args.json_out:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(text + "\n")
        print(f"wrote {args.json_out}")
    else:
        print(text)


if __name__ == "__main__":
    main()
