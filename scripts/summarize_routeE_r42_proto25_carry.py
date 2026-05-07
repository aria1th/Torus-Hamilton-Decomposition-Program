#!/usr/bin/env python3
"""Probe the R42 25->3 edge as a c-band carry pattern.

The R42 qtime interval profile localized the only multi-point interval edge to
25 -> 3.  This script regenerates that edge on sampled witnesses and checks the
simple c-band support grammar:

  c = 6q + 5, m = 8c + 2
  doubletons: [1+3n, 2+3n], 0 <= n <= (2c-4)/3
  singletons: 2c+1+6j, 0 <= j <= (c-2)/3
              2c+3+6j, 0 <= j <= (c-5)/3
              4c

It also records the observed qtime slope alphabet.  This is not a proof of the
branch: it is a focused diagnostic for the next clock-carry refinement.
"""

from __future__ import annotations

import argparse
import json
import tempfile
from pathlib import Path
from typing import Any

import summarize_routeE_r42_boundary_quotient as r42
import summarize_routeE_r42_boundary_block_transducer as bt
from summarize_routeE_r42_mod96_edge_partitions import affine_coeffs, intervals


DEFAULT_BIN = Path(tempfile.gettempdir()) / "routeE_allpair_cpp_v1_2"


def parse_range(text: str) -> list[int]:
    if ":" in text:
        start, end = [int(part) for part in text.split(":", 1)]
        return list(range(start, end + 1))
    return [int(part) for part in text.split(",") if part]


def expected_intervals(c: int) -> list[tuple[int, int, str]]:
    out: list[tuple[int, int, str]] = []
    for n in range((2 * c - 4) // 3 + 1):
        lo = 1 + 3 * n
        out.append((lo, lo + 1, "double_1mod3"))
    for j in range((c - 2) // 3 + 1):
        value = 2 * c + 1 + 6 * j
        out.append((value, value, "single_2c1_6j"))
    for j in range((c - 5) // 3 + 1):
        value = 2 * c + 3 + 6 * j
        out.append((value, value, "single_2c3_6j"))
    out.append((4 * c, 4 * c, "single_endpoint_4c"))
    return sorted(out)


def collect_sample(binary: Path, q: int, workdir: Path) -> dict[str, Any]:
    c = 6 * q + 5
    m = 8 * c + 2
    cap = max(10_000, 10 * m * m)
    csv_path = workdir / f"r42_proto25_q{q}.csv"
    proc = r42.subprocess.run(
        [str(binary), "dump-csv", str(m), str(c), str(c), str(cap), str(csv_path)],
        cwd=r42.REPO,
        text=True,
        stdout=r42.subprocess.PIPE,
        stderr=r42.subprocess.PIPE,
        check=False,
    )
    if proc.returncode != 0:
        return {
            "q": q,
            "c": c,
            "m": m,
            "ok": False,
            "returncode": proc.returncode,
            "stderr_tail": proc.stderr.strip().splitlines()[-5:],
        }

    rows = r42.load_rows(csv_path)
    blocks = bt.block_rows(r42.boundary_return_rows(rows), m)
    by_node: dict[tuple[str, int], int] = {}
    by_member: dict[tuple[str, int], dict[str, Any]] = {}
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
    members = sorted(groups[(25, 3)], key=lambda row: row["src_a"])

    actual = []
    slope_values = set()
    for lo, hi in intervals([member["src_a"] for member in members]):
        sub = [member for member in members if lo <= member["src_a"] <= hi]
        coeffs = affine_coeffs([(member["src_a"], member["qtime"]) for member in sub])
        if coeffs is None:
            actual.append(
                {
                    "lo": lo,
                    "hi": hi,
                    "length": len(sub),
                    "qtime_affine": False,
                    "qtime_slope": None,
                    "qtime_intercept": None,
                }
            )
            continue
        slope_values.add(coeffs[0])
        actual.append(
            {
                "lo": lo,
                "hi": hi,
                "length": len(sub),
                "qtime_affine": True,
                "qtime_slope": coeffs[0],
                "qtime_intercept": coeffs[1],
                "band_lo": lo // c,
                "u_lo": lo % c,
                "band_hi": hi // c,
                "u_hi": hi % c,
            }
        )

    expected = expected_intervals(c)
    actual_support = [(row["lo"], row["hi"]) for row in actual]
    expected_support = [(lo, hi) for lo, hi, _ in expected]
    expected_type_by_interval = {(lo, hi): kind for lo, hi, kind in expected}
    expected_slope_alphabet = [0, 4 * c + 3, 12 * c + 5]
    length_counts = {
        str(length): sum(1 for row in actual if row["length"] == length)
        for length in sorted({row["length"] for row in actual})
    }
    type_counts = {
        kind: sum(1 for lo, hi, row_kind in expected if row_kind == kind)
        for kind in sorted({kind for _, _, kind in expected})
    }
    return {
        "q": q,
        "c": c,
        "m": m,
        "ok": True,
        "edge": "25 -> 3",
        "member_count": len(members),
        "interval_count": len(actual),
        "expected_member_count": 2 * c,
        "expected_interval_count": (4 * c + 1) // 3,
        "length_counts": length_counts,
        "expected_length_counts": {
            "1": (2 * c + 2) // 3,
            "2": (2 * c - 1) // 3,
        },
        "type_counts": type_counts,
        "support_matches_carry_grammar": actual_support == expected_support,
        "all_intervals_qtime_affine": all(row["qtime_affine"] for row in actual),
        "qtime_slope_values": sorted(slope_values),
        "expected_qtime_slope_alphabet": expected_slope_alphabet,
        "qtime_slopes_within_expected_alphabet": set(slope_values).issubset(
            set(expected_slope_alphabet)
        ),
        "first_intervals": [
            {
                **row,
                "expected_type": expected_type_by_interval.get((row["lo"], row["hi"])),
            }
            for row in actual[:24]
        ],
        "last_intervals": [
            {
                **row,
                "expected_type": expected_type_by_interval.get((row["lo"], row["hi"])),
            }
            for row in actual[-12:]
        ],
    }


def build_summary(q_values: list[int], binary: Path, compile_binary: bool) -> dict[str, Any]:
    if compile_binary:
        r42.compile_checker(binary)
    with tempfile.TemporaryDirectory(prefix="routeE-r42-proto25-") as tmp:
        samples = [collect_sample(binary, q, Path(tmp)) for q in q_values]
    return {
        "schema": "routeE_r42_proto25_carry_v1",
        "family": "R42, c=6*q+5, m=8*c+2, x=z=c",
        "q_values": q_values,
        "samples": samples,
        "summary": {
            "all_samples_ok": all(sample.get("ok") for sample in samples),
            "all_support_matches_carry_grammar": all(
                sample.get("support_matches_carry_grammar") for sample in samples
            ),
            "all_intervals_qtime_affine": all(
                sample.get("all_intervals_qtime_affine") for sample in samples
            ),
            "all_qtime_slopes_within_expected_alphabet": all(
                sample.get("qtime_slopes_within_expected_alphabet")
                for sample in samples
            ),
            "expected_support_grammar": [
                "[1+3n, 2+3n], 0 <= n <= (2c-4)/3",
                "{2c+1+6j}, 0 <= j <= (c-2)/3",
                "{2c+3+6j}, 0 <= j <= (c-5)/3",
                "{4c}",
            ],
            "expected_qtime_slope_alphabet": [
                "0",
                "4c + 3",
                "12c + 5",
            ],
        },
        "promotion_impact": {
            "closes_residue": False,
            "pointwise_equations_closed": False,
            "no_early_closed": False,
            "diagnosis": (
                "The prototype 25->3 edge has a stable c-band support grammar "
                "and a small qtime slope alphabet on the sampled witnesses.  "
                "This supports the clock-carry-transducer hypothesis, but it "
                "does not prove the full qtime law or no-early condition."
            ),
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--q-values", default="6:9")
    parser.add_argument("--binary", type=Path, default=DEFAULT_BIN)
    parser.add_argument("--no-compile", action="store_true")
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()
    payload = build_summary(parse_range(args.q_values), args.binary, not args.no_compile)
    print("schema", payload["schema"])
    print("all_samples_ok", payload["summary"]["all_samples_ok"])
    print(
        "all_support_matches_carry_grammar",
        payload["summary"]["all_support_matches_carry_grammar"],
    )
    print(
        "all_qtime_slopes_within_expected_alphabet",
        payload["summary"]["all_qtime_slopes_within_expected_alphabet"],
    )
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
        print(f"wrote {args.json_out}")


if __name__ == "__main__":
    main()
