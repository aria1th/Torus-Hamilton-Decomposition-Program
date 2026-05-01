#!/usr/bin/env python3
"""Verifier for the D5 even Route-E research bundle.

This is an audit artifact, not a symbolic proof.  It absorbs the independent
checks from `d5_even_routeE_bundle_v0_1.zip`:

* finite schedules for m = 4,6,...,20;
* the normalized Route-E core first-return check;
* the open-port section formula/cycle check used by the periodic framework.
"""
from __future__ import annotations

import argparse
import json
from collections import Counter
from math import gcd
from pathlib import Path
from typing import Dict, Iterable, List, Tuple

MaskTable = Dict[int, Tuple[int, int, int, int, int]]
State = Tuple[int, int, int, int, int]
Symbol = Tuple[str, int]

REPS = [0, 1, 3, 5, 7, 11, 31]
OLD: MaskTable = {
    0: (0, 1, 2, 3, 4),
    1: (0, 1, 3, 2, 4),
    3: (4, 1, 3, 2, 0),
    5: (4, 1, 3, 0, 2),
    7: (1, 0, 3, 4, 2),
    11: (4, 3, 0, 2, 1),
    31: (0, 1, 2, 3, 4),
}
PERT: MaskTable = dict(OLD)
PERT[7] = (1, 4, 3, 0, 2)
PERT[11] = (4, 0, 3, 2, 1)

M4_ROWS: List[List[Symbol]] = [
    [("C", 0), ("E", 2), ("O", 4), ("O", 0)],
    [("C", 1), ("E", 0), ("O", 2), ("O", 3)],
    [("C", 2), ("E", 3), ("O", 0), ("O", 1)],
    [("C", 3), ("E", 1), ("O", 3), ("O", 4)],
    [("C", 4), ("E", 4), ("O", 1), ("O", 2)],
]

ONE_E_SCHEDULES = {
    6: {"slot": 0, "counts": (0, 0, 1, 3, 1)},
    8: {"slot": 0, "counts": (2, 0, 0, 3, 2)},
    10: {"slot": 0, "counts": (0, 3, 3, 2, 1)},
    12: {"slot": 0, "counts": (1, 2, 3, 5, 0)},
    14: {"slot": 0, "counts": (4, 2, 4, 1, 2)},
    16: {"slot": 4, "counts": (13, 0, 1, 0, 1)},
    18: {"slot": 0, "counts": (4, 4, 0, 1, 8)},
    20: {"slot": 0, "counts": (4, 2, 4, 9, 0)},
}

SECTION_EXAMPLES = [
    (10, 0, 8, 1),
    (10, 6, 2, 1),
    (12, 4, 2, 5),
    (14, 6, 2, 5),
    (18, 8, 4, 5),
    (20, 0, 10, 9),
    (22, 6, 12, 3),
    (26, 2, 16, 7),
    (28, 0, 10, 17),
]


def rotmask(mask: int, k: int) -> int:
    out = 0
    for x in range(5):
        if mask & (1 << x):
            out |= 1 << ((x + k) % 5)
    return out


CANON = {}
for mask in range(32):
    for k in range(5):
        rep = rotmask(mask, -k)
        if rep in REPS:
            CANON[mask] = (rep, k)
            break


def lam(table: MaskTable, shifted_mask: int, slot: int) -> int:
    rep, k = CANON[shifted_mask]
    return (table[rep][(slot - k) % 5] + k) % 5


def states_idx(m: int) -> Tuple[List[State], Dict[State, int]]:
    states: List[State] = []
    idx: Dict[State, int] = {}
    for a in range(m):
        for b in range(m):
            for c in range(m):
                for d in range(m):
                    e = (-a - b - c - d) % m
                    w = (a, b, c, d, e)
                    idx[w] = len(states)
                    states.append(w)
    return states, idx


def shifted_zero_mask(w: State) -> int:
    mask = 0
    for i, x in enumerate(w):
        if x == 0:
            mask |= 1 << ((i - 1) % 5)
    return mask


def q_step(m: int, idx: Dict[State, int], w: State, direction: int) -> int:
    ww = list(w)
    if direction < 4:
        ww[direction] = (ww[direction] + 1) % m
        ww[4] = (ww[4] - 1) % m
    return idx[tuple(ww)]  # type: ignore[arg-type]


def build_symbol_maps(m: int):
    states, idx = states_idx(m)
    maps = {}
    for a in range(5):
        maps[("C", a)] = [q_step(m, idx, w, a) for w in states]
    for tag, table in [("O", OLD), ("E", PERT)]:
        for slot in range(5):
            maps[(tag, slot)] = [
                q_step(m, idx, w, lam(table, shifted_zero_mask(w), slot))
                for w in states
            ]
    return states, idx, maps


def cycle_lengths(perm: List[int]) -> List[int]:
    seen = [False] * len(perm)
    out = []
    for i in range(len(perm)):
        if seen[i]:
            continue
        x = i
        length = 0
        while not seen[x]:
            seen[x] = True
            length += 1
            x = perm[x]
        out.append(length)
    return sorted(out)


def compose_maps(size: int, maps: Dict[Symbol, List[int]], row: List[Symbol]) -> List[int]:
    perm = list(range(size))
    for sym in row:
        mp = maps[sym]
        perm = [mp[x] for x in perm]
    return perm


def verify_m4_schedule():
    m = 4
    _, _, maps = build_symbol_maps(m)
    size = m**4
    layer_columns = []
    for t in range(m):
        col = [M4_ROWS[c][t] for c in range(5)]
        layer_columns.append(col)
        assert len({slot for _, slot in col}) == 5
        if t == 0:
            assert all(fam == "C" for fam, _ in col)
        elif t == 1:
            assert all(fam == "E" for fam, _ in col)
        else:
            assert all(fam == "O" for fam, _ in col)
    lengths = [cycle_lengths(compose_maps(size, maps, row)) for row in M4_ROWS]
    return {
        "m": m,
        "type": "finite_m4_C_E_O_schedule",
        "rows": M4_ROWS,
        "layer_columns": layer_columns,
        "cycle_lengths": lengths,
        "ok": all(length == [size] for length in lengths),
    }


def normalize_counts_to_slot0(
    slot: int, counts: Tuple[int, int, int, int, int]
) -> Tuple[int, int, int, int, int]:
    return tuple(counts[(i + slot) % 5] for i in range(5))  # type: ignore[return-value]


def count_hit_summary(slot: int, counts: Tuple[int, int, int, int, int]) -> dict:
    normalized = normalize_counts_to_slot0(slot, counts)
    return {
        "slot": slot,
        "counts": counts,
        "normalized_counts_slot0": normalized,
        "open_port_normal_form": normalized[0] == 0 and normalized[4] == 0,
    }


def one_e_rows(m: int, slot: int, counts: Tuple[int, int, int, int, int]):
    rel: List[Symbol] = []
    for a, n in enumerate(counts):
        rel.extend([("C", a)] * n)
    rel.append(("E", slot))
    return [[(fam, (a + color) % 5) for fam, a in rel] for color in range(5)]


def verify_one_e_schedule(m: int, slot: int, counts: Tuple[int, int, int, int, int]):
    _, _, maps = build_symbol_maps(m)
    size = m**4
    rows = one_e_rows(m, slot, counts)
    assert len(rows[0]) == m
    lengths = [cycle_lengths(compose_maps(size, maps, row)) for row in rows]
    return {
        "m": m,
        "type": "one_Lambda_E_layer_plus_constant_offsets",
        "slot": slot,
        "counts": counts,
        "normalized_counts_slot0": normalize_counts_to_slot0(slot, counts),
        "relative_layers": [("C", a, n) for a, n in enumerate(counts) if n] + [("E", slot, 1)],
        "cycle_lengths": lengths,
        "ok": all(length == [size] for length in lengths),
    }


def verify_schedule_table() -> List[dict]:
    results = [verify_m4_schedule()]
    for m, data in ONE_E_SCHEDULES.items():
        results.append(verify_one_e_schedule(m, data["slot"], data["counts"]))
    return results


def core_p(w: State) -> int:
    return lam(PERT, shifted_zero_mask(w), 0)


def core_perm(m: int) -> Tuple[List[int], List[State], Dict[State, int]]:
    drift = (-1, 1, 0, -1, 0)
    states, idx = states_idx(m)
    out = [0] * len(states)
    for n, w in enumerate(states):
        p = core_p(w)
        y = list(w)
        for i, value in enumerate(drift):
            y[i] = (y[i] + value) % m
        y[p] = (y[p] + 1) % m
        out[n] = idx[tuple(y)]  # type: ignore[arg-type]
    return out, states, idx


def first_return(perm: List[int], section: List[int]) -> Tuple[Dict[int, int], Dict[int, int]]:
    section_set = set(section)
    returns = {}
    times = {}
    for x in section:
        y = perm[x]
        time = 1
        while y not in section_set:
            y = perm[y]
            time += 1
            if time > len(perm) + 1000:
                raise RuntimeError((x, time))
        returns[x] = y
        times[x] = time
    return returns, times


def core_section_indices(states: List[State]) -> List[int]:
    return [i for i, w in enumerate(states) if w[0] == 0 and w[3] == 0 and w[4] != 0]


def expected_core_phi(m: int, a: int, b: int) -> Tuple[int, int]:
    if a == 0:
        if b == 1:
            return (m - 1, 0)
        return (m - 1, b)
    return ((a - 1) % m, (b + 1) % m)


def expected_core_time(m: int, a: int, b: int) -> int:
    common = m * (m + 1)
    if a == 0 and b == 1:
        return common - 2
    if b == m - 1 and a == 2:
        return common + 5 * m - 4
    if b == m - 1 and 3 <= a <= m - 1:
        return common + (m - 2)
    return common


def verify_core_m(m: int) -> dict:
    perm, states, _ = core_perm(m)
    lengths = cycle_lengths(perm)
    section = core_section_indices(states)
    returns, times = first_return(perm, section)
    bad = []
    for x in section:
        w = states[x]
        a, b = w[1], w[2]
        y = states[returns[x]]
        got = (y[1], y[2])
        expected = expected_core_phi(m, a, b)
        expected_time = expected_core_time(m, a, b)
        if got != expected or times[x] != expected_time:
            bad.append(
                {
                    "from": (a, b),
                    "got": got,
                    "expected": expected,
                    "time": times[x],
                    "expected_time": expected_time,
                }
            )
            if len(bad) > 10:
                break
    return {
        "m": m,
        "cycle_lengths": lengths,
        "single_cycle": lengths == [m**4],
        "section_size": len(section),
        "first_return_formula_ok": not bad,
        "first_return_time_sum": sum(times.values()),
        "time_distribution": dict(sorted(Counter(times.values()).items())),
        "bad_examples": bad,
    }


def verify_core(moduli: Iterable[int]) -> List[dict]:
    return [verify_core_m(m) for m in moduli]


def one_e_return_step_with_slot(
    m: int, slot: int, counts: Tuple[int, int, int, int, int], w: State
) -> State:
    p = lam(PERT, shifted_zero_mask(w), slot)
    y = list(w)
    for i, count in enumerate(counts):
        y[i] = (y[i] + count) % m
    y[p] = (y[p] + 1) % m
    return tuple(y)  # type: ignore[return-value]


def one_e_return_step(
    m: int, counts: Tuple[int, int, int, int, int], w: State
) -> State:
    return one_e_return_step_with_slot(m, 0, counts, w)


def expected_section_h(m: int, a_count: int, b_count: int, a: int, b: int):
    if (a + b) % m != 0:
        return ((a + a_count + 1) % m, (b + b_count) % m)
    return ((a + a_count) % m, (b + b_count + 1) % m)


def h_cycle_lengths(m: int, a_count: int, c_count: int) -> List[int]:
    seen = set()
    lengths = []
    for sig in range(m):
        for a in range(m):
            if (sig, a) in seen:
                continue
            x = (sig, a)
            length = 0
            while x not in seen:
                seen.add(x)
                length += 1
                sig, a = x
                x = ((sig - c_count) % m, (a + a_count + 1 - (1 if sig == 0 else 0)) % m)
            lengths.append(length)
    return sorted(lengths)


def check_section_case(m: int, a_count: int, b_count: int, c_count: int) -> dict:
    assert a_count + b_count + c_count == m - 1
    counts = (0, a_count, b_count, c_count, 0)
    exceptions = []
    bad = []
    for a in range(m):
        for b in range(m):
            c = (-a - b) % m
            if (a, b, c) == (0, 0, 0):
                continue
            w = (0, a, b, c, 0)
            y = one_e_return_step(m, counts, w)
            if y == (0, 0, 0, 0, 0):
                exceptions.append((a, b))
                continue
            if not (y[0] == 0 and y[4] == 0 and y != (0, 0, 0, 0, 0)):
                bad.append({"from": w, "to": y, "reason": "not back to section"})
                continue
            got = (y[1], y[2])
            expected = expected_section_h(m, a_count, b_count, a, b)
            if got != expected:
                bad.append({"from": w, "to": y, "got": got, "expected": expected})
            if len(bad) > 5:
                break
        if len(bad) > 5:
            break
    lengths = h_cycle_lengths(m, a_count, c_count)
    return {
        "m": m,
        "A": a_count,
        "B": b_count,
        "C": c_count,
        "C_unit": gcd(c_count, m) == 1,
        "section_formula_ok": not bad,
        "exception_count": len(exceptions),
        "exception_points": exceptions[:5],
        "H_cycle_lengths": lengths,
        "H_single": lengths == [m * m],
        "bad_examples": bad[:5],
    }


def scan_open_port_section_cases(moduli: Iterable[int], limit: int) -> List[dict]:
    results = []
    for m in moduli:
        hits = []
        checked = 0
        for c_count in range(1, m):
            if gcd(c_count, m) != 1:
                continue
            for a_count in range(m - c_count):
                b_count = m - 1 - a_count - c_count
                checked += 1
                result = check_section_case(m, a_count, b_count, c_count)
                if (
                    result["C_unit"]
                    and result["section_formula_ok"]
                    and result["H_single"]
                ):
                    hits.append(result)
                    if len(hits) >= limit:
                        break
            if len(hits) >= limit:
                break
        results.append(
            {
                "m": m,
                "checked": checked,
                "hit_count": len(hits),
                "first_hits": hits,
                "ok": bool(hits),
            }
        )
    return results


def one_e_single_cycle(
    m: int,
    slot: int,
    counts: Tuple[int, int, int, int, int],
    states: List[State],
    idx: Dict[State, int],
) -> bool:
    seen = bytearray(len(states))
    state = 0
    for _ in range(len(states)):
        if seen[state]:
            return False
        seen[state] = 1
        state = idx[one_e_return_step_with_slot(m, slot, counts, states[state])]
    return state == 0


def weak_compositions(total: int, parts: int):
    if parts == 1:
        yield (total,)
        return
    for value in range(total + 1):
        for tail in weak_compositions(total - value, parts - 1):
            yield (value,) + tail


def scan_one_e_full_count_cases(moduli: Iterable[int], limit: int) -> List[dict]:
    results = []
    for m in moduli:
        states, idx = states_idx(m)
        hits = []
        checked = 0
        for slot in range(5):
            for counts in weak_compositions(m - 1, 5):
                checked += 1
                if one_e_single_cycle(m, slot, counts, states, idx):
                    hits.append(count_hit_summary(slot, counts))
                    if len(hits) >= limit:
                        break
            if len(hits) >= limit:
                break
        results.append(
            {
                "m": m,
                "checked": checked,
                "hit_count": len(hits),
                "first_hits": hits,
                "ok": bool(hits),
            }
        )
    return results


def scan_open_port_full_cases(moduli: Iterable[int], limit: int) -> List[dict]:
    results = []
    for m in moduli:
        states, idx = states_idx(m)
        hits = []
        section_hits = 0
        full_checked = 0
        for c_count in range(1, m):
            if gcd(c_count, m) != 1:
                continue
            for a_count in range(m - c_count):
                b_count = m - 1 - a_count - c_count
                section = check_section_case(m, a_count, b_count, c_count)
                if not (
                    section["C_unit"]
                    and section["section_formula_ok"]
                    and section["H_single"]
                ):
                    continue
                section_hits += 1
                full_checked += 1
                counts = (0, a_count, b_count, c_count, 0)
                if one_e_single_cycle(m, 0, counts, states, idx):
                    hit = dict(section)
                    hit.update(count_hit_summary(0, counts))
                    hit["full_single"] = True
                    hits.append(hit)
                    if len(hits) >= limit:
                        break
            if len(hits) >= limit:
                break
        results.append(
            {
                "m": m,
                "section_hits": section_hits,
                "full_checked": full_checked,
                "full_hit_count": len(hits),
                "first_full_hits": hits,
                "ok": bool(hits),
            }
        )
    return results


def parse_moduli(text: str) -> List[int]:
    return [int(part) for part in text.split(",") if part.strip()]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--mode", choices=["all", "schedule", "core", "section"], default="all")
    parser.add_argument("--core-moduli", default="2,4,6,8,10,12,14,16,18,20")
    parser.add_argument(
        "--section-scan-moduli",
        help="comma-separated even moduli for open-port section triple search",
    )
    parser.add_argument("--section-scan-limit", type=int, default=3)
    parser.add_argument(
        "--full-scan-moduli",
        help="comma-separated even moduli for open-port section triples that are full cycles",
    )
    parser.add_argument("--full-scan-limit", type=int, default=5)
    parser.add_argument(
        "--count-scan-moduli",
        help="comma-separated even moduli for full one-Lambda_E count/slot scans",
    )
    parser.add_argument("--count-scan-limit", type=int, default=10)
    parser.add_argument("--json-out")
    args = parser.parse_args()

    output = {}
    if args.mode in {"all", "schedule"}:
        output["schedule"] = verify_schedule_table()
    if args.mode in {"all", "core"}:
        output["core"] = verify_core(parse_moduli(args.core_moduli))
    if args.mode in {"all", "section"}:
        output["section"] = [check_section_case(*case) for case in SECTION_EXAMPLES]
    if args.section_scan_moduli:
        output["section_scan"] = scan_open_port_section_cases(
            parse_moduli(args.section_scan_moduli), args.section_scan_limit
        )
    if args.full_scan_moduli:
        output["open_port_full_scan"] = scan_open_port_full_cases(
            parse_moduli(args.full_scan_moduli), args.full_scan_limit
        )
    if args.count_scan_moduli:
        output["one_e_full_count_scan"] = scan_one_e_full_count_cases(
            parse_moduli(args.count_scan_moduli), args.count_scan_limit
        )

    text = json.dumps(output, indent=2)
    if args.json_out:
        Path(args.json_out).write_text(text + "\n")
    print(text)


if __name__ == "__main__":
    main()
