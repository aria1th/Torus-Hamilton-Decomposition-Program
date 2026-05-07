#!/usr/bin/env python3
"""Dump raw zero-clock trace signatures for the unresolved R42 atom.

The threshold/residue feature alphabet failed to uniformly explain the atom

  20->26|L1|B7:7|R0:0.

This script goes one level lower.  For each sampled source point in that atom,
it reconstructs the all-pair first-return trace and records selector counts,
zero-winner counts, and modular carry totals.  This is a search artifact for a
new state variable, not a proof.
"""

from __future__ import annotations

import argparse
import json
import tempfile
from collections import Counter
from pathlib import Path
from typing import Any

import summarize_routeE_r42_boundary_quotient as r42
import summarize_routeE_r42_boundary_block_transducer as bt
from summarize_routeE_r42_carry_qtime_atoms import affine_coeffs, intervals
from summarize_routeE_r42_carry_support_atoms import atom_key


DEFAULT_BIN = Path(tempfile.gettempdir()) / "routeE_allpair_cpp_v1_2"
DEFAULT_ATOM = "20->26|L1|B7:7|R0:0"
PI = [0, 0, 0, 0, 1, 1, 1, 2, 2, 3]
PJ = [1, 2, 3, 4, 2, 3, 4, 3, 4, 4]
LABELS = ["Z", "01", "02", "03", "04", "12", "13", "14", "23", "24", "34"]
SEL = [
    0, 0, 0, 4, 4, 4, 1, 1,
    1, 1, 3, 4, 4, 4, 3, 0,
    0, 0, 0, 3, 2, 4, 2, 0,
    1, 1, 1, 0, 2, 0, 0, 0,
]


def parse_q_values(spec: str) -> list[int]:
    if ":" in spec:
        lo, hi = spec.split(":", 1)
        return list(range(int(lo), int(hi) + 1))
    return [int(part) for part in spec.split(",") if part]


def inv_mod(a: int, m: int) -> int:
    return pow(a % m, -1, m)


def selector(w: list[int]) -> int:
    idx = 0
    if w[1] == 0:
        idx |= 1
    if w[2] == 0:
        idx |= 2
    if w[3] == 0:
        idx |= 4
    if w[4] == 0:
        idx |= 8
    if w[0] == 0:
        idx |= 16
    return SEL[idx]


def inc_for_selector(m: int, x: int, z: int, s: int) -> list[int]:
    inc = [x % m, (m - 1 - x - z) % m, 0, z % m, 0]
    inc[s] = (inc[s] + 1) % m
    return inc


def event_times(w: list[int], m: int, inc: list[int]) -> list[int | None]:
    out: list[int | None] = []
    for ww, ii in zip(w, inc):
        ww %= m
        ii %= m
        if ii == 0:
            out.append(None)
            continue
        if ww == 0:
            out.append(1)
            continue
        g = __import__("math").gcd(ii, m)
        if ww % g:
            out.append(None)
            continue
        mod = m // g
        t = ((-ww // g) % mod) * inv_mod(ii // g, mod) % mod
        if t == 0:
            t = mod
        out.append(t)
    return out


def step_jump(w: list[int], m: int, x: int, z: int) -> dict[str, Any]:
    s = selector(w)
    inc = inc_for_selector(m, x, z, s)
    times = event_times(w, m, inc)
    best = min(t for t in times if t is not None)
    winners = [i for i, t in enumerate(times) if t == best]
    raw = [w[i] + best * inc[i] for i in range(5)]
    carries = [value // m for value in raw]
    nw = [value % m for value in raw]
    return {
        "selector": s,
        "inc": inc,
        "step": best,
        "winners": winners,
        "winner_mask": "".join("1" if i in winners else "0" for i in range(5)),
        "carries": carries,
        "next": nw,
    }


def idx_to_w(idx: int, m: int) -> list[int]:
    w = [0, 0, 0, 0, 0]
    if idx == 0:
        return w
    t = idx - 1
    p = t // (m - 1)
    a = t % (m - 1) + 1
    i, j = PI[p], PJ[p]
    w[i] = a
    w[j] = (m - a) % m
    return w


def pair_idx_from_w(w: list[int], m: int) -> int:
    nz = [i for i, value in enumerate(w) if value % m != 0]
    if not nz:
        return 0
    if len(nz) != 2:
        return -1
    a, b = nz
    if (w[a] + w[b]) % m != 0:
        return -1
    i, j = min(a, b), max(a, b)
    p = next(k for k, pair in enumerate(zip(PI, PJ)) if pair == (i, j))
    aa = w[i] % m
    return 1 + p * (m - 1) + (aa - 1)


def node_idx(label: str, a: int, m: int) -> int:
    if label == "Z":
        return 0
    p = LABELS.index(label) - 1
    return 1 + p * (m - 1) + (a - 1)


def trace_idx(m: int, x: int, z: int, idx: int, cap: int) -> dict[str, Any]:
    w = idx_to_w(idx, m)
    total = 0
    selector_counts: Counter[str] = Counter()
    winner_counts: Counter[str] = Counter()
    carry_totals = [0, 0, 0, 0, 0]
    step_residue_counts: Counter[str] = Counter()
    first_events = []
    last_events = []
    dst = -1
    for event_index in range(cap):
        jump = step_jump(w, m, x, z)
        total += jump["step"]
        selector_counts[str(jump["selector"])] += 1
        winner_counts[jump["winner_mask"]] += 1
        for i, carry in enumerate(jump["carries"]):
            carry_totals[i] += carry
        step_residue_counts[str(jump["step"] % 8)] += 1
        event = {
            "event": event_index,
            "selector": jump["selector"],
            "step": jump["step"],
            "winner_mask": jump["winner_mask"],
            "carries": jump["carries"],
            "w_before": w,
            "w_after": jump["next"],
        }
        if len(first_events) < 8:
            first_events.append(event)
        last_events.append(event)
        if len(last_events) > 8:
            last_events.pop(0)
        w = jump["next"]
        dst = pair_idx_from_w(w, m)
        if dst >= 0:
            return {
                "dst_idx": dst,
                "time": total,
                "events": event_index + 1,
                "selector_counts": dict(sorted(selector_counts.items())),
                "winner_counts": dict(sorted(winner_counts.items())),
                "carry_totals": carry_totals,
                "step_residue_mod8_counts": dict(sorted(step_residue_counts.items())),
                "first_events": first_events,
                "last_events": last_events,
            }
    return {"dst_idx": -1, "time": total, "events": cap}


def atom_rows_for_sample(binary: Path, q: int, atom: str, workdir: Path) -> list[dict[str, Any]]:
    c = 6 * q + 5
    m = 8 * c + 2
    cap = max(10_000, 10 * m * m)
    csv_path = workdir / f"r42_raw_trace_q{q}.csv"
    proc = r42.subprocess.run(
        [str(binary), "dump-csv", str(m), str(c), str(c), str(cap), str(csv_path)],
        cwd=r42.REPO,
        text=True,
        stdout=r42.subprocess.PIPE,
        stderr=r42.subprocess.PIPE,
        check=False,
    )
    if proc.returncode != 0:
        raise RuntimeError(proc.stderr)
    rows = r42.load_rows(csv_path)
    blocks = bt.block_rows(r42.boundary_return_rows(rows), m)
    by_node = {}
    by_member = {}
    for index, block in enumerate(blocks):
        for member in block["_members"]:
            key = (member["src_label"], member["src_a"])
            by_node[key] = index
            by_member[key] = member
    groups: dict[tuple[int, int], list[dict[str, Any]]] = {}
    for key, member in by_member.items():
        src_block = by_node[key]
        dst_block = by_node[(member["dst_label"], member["dst_a"])]
        groups.setdefault((src_block, dst_block), []).append(member)

    out = []
    for (src, dst), members in sorted(groups.items()):
        members = sorted(members, key=lambda row: row["src_a"])
        if affine_coeffs([(member["src_a"], member["qtime"]) for member in members]):
            continue
        for lo, hi in intervals([member["src_a"] for member in members]):
            sub = [member for member in members if lo <= member["src_a"] <= hi]
            coeffs = affine_coeffs([(member["src_a"], member["qtime"]) for member in sub])
            if coeffs is None:
                continue
            row = {
                "src": src,
                "dst": dst,
                "lo": lo,
                "hi": hi,
                "length": hi - lo + 1,
                "band_lo": lo // c,
                "band_hi": hi // c,
                "u_lo_mod6": (lo % c) % 6,
                "u_hi_mod6": (hi % c) % 6,
                "j": ((lo % c) - ((lo % c) % 6)) // 6,
                "qtime_slope": coeffs[0],
                "qtime_intercept": coeffs[1],
            }
            row["atom"] = atom_key(row)
            if row["atom"] != atom:
                continue
            for member in sub:
                row2 = dict(row)
                row2["src_label"] = member["src_label"]
                row2["src_a"] = member["src_a"]
                row2["dst_label"] = member["dst_label"]
                row2["dst_a"] = member["dst_a"]
                row2["qtime"] = member["qtime"]
                row2["qsteps"] = member["qsteps"]
                row2["path"] = member["path"]
                out.append(row2)
    return out


def build_summary(q_values: list[int], atom: str, binary: Path, compile_binary: bool) -> dict[str, Any]:
    if compile_binary:
        r42.compile_checker(binary)
    samples = []
    with tempfile.TemporaryDirectory(prefix="routeE-r42-raw-trace-") as tmp:
        workdir = Path(tmp)
        for q in q_values:
            c = 6 * q + 5
            m = 8 * c + 2
            for row in atom_rows_for_sample(binary, q, atom, workdir):
                idx = node_idx(row["src_label"], row["src_a"], m)
                trace = trace_idx(m, c, c, idx, cap=max(10_000, 10 * m * m))
                samples.append(
                    {
                        "q": q,
                        "parity": "even" if q % 2 == 0 else "odd",
                        "s": q // 2 if q % 2 == 0 else (q - 1) // 2,
                        "m": m,
                        "c": c,
                        "j": row["j"],
                        "src_label": row["src_label"],
                        "src_a": row["src_a"],
                        "expected_dst_label": row["dst_label"],
                        "expected_dst_a": row["dst_a"],
                        "expected_qtime": row["qtime"],
                        "trace": trace,
                        "trace_matches": trace["time"] == row["qtime"],
                    }
                )
    parity_summary = {}
    for parity in ("even", "odd"):
        part = [sample for sample in samples if sample["parity"] == parity]
        parity_summary[parity] = {
            "sample_count": len(part),
            "q_values": sorted({sample["q"] for sample in part}),
            "all_trace_matches": all(sample["trace_matches"] for sample in part),
            "event_counts": sorted({sample["trace"]["events"] for sample in part}),
            "winner_keys": sorted(
                {
                    key
                    for sample in part
                    for key in sample["trace"].get("winner_counts", {})
                }
            ),
        }
    return {
        "schema": "routeE_r42_unresolved_atom_raw_trace_v1",
        "atom": atom,
        "q_values": q_values,
        "sample_count": len(samples),
        "parity_summary": parity_summary,
        "samples": samples,
        "promotion_impact": {
            "closes_residue": False,
            "pointwise_equations_closed": False,
            "no_early_closed": False,
            "diagnosis": (
                "Raw zero-clock traces for the unresolved R42 atom.  This is "
                "intended to seed a new state variable if R42 is revisited."
            ),
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--q-values", default="6,7,8,9,10,11")
    parser.add_argument("--atom", default=DEFAULT_ATOM)
    parser.add_argument("--binary", type=Path, default=DEFAULT_BIN)
    parser.add_argument("--no-compile", action="store_true")
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()
    payload = build_summary(
        parse_q_values(args.q_values),
        atom=args.atom,
        binary=args.binary,
        compile_binary=not args.no_compile,
    )
    print("schema", payload["schema"])
    print("atom", payload["atom"])
    print("sample_count", payload["sample_count"])
    print("parity_summary", payload["parity_summary"])
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
        print(f"wrote {args.json_out}")


if __name__ == "__main__":
    main()
