#!/usr/bin/env python3
"""Summarize c-band support atoms for all R42 qtime-missing edges.

This is a support-level companion to the 25->3 carry probe.  It regenerates
sample witnesses, extracts the 22 edges whose qtime is not affine on the whole
edge, and records whether their source-a support is stable after splitting into

  edge, interval length, c-band, and u mod 6.

For each such atom it fits the j-range endpoints in the branch parameter s.
This is evidence for a finite c-band clock-carry transducer; it is not a
pointwise qtime or no-early proof.
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
from summarize_routeE_r42_qtime_interval_profiles import affine_formula


DEFAULT_BIN = Path(tempfile.gettempdir()) / "routeE_allpair_cpp_v1_2"


def parse_range(text: str) -> list[int]:
    if ":" in text:
        start, end = [int(part) for part in text.split(":", 1)]
        return list(range(start, end + 1))
    return [int(part) for part in text.split(",") if part]


def atom_key(row: dict[str, Any]) -> str:
    return (
        f"{row['src']}->{row['dst']}|L{row['length']}|"
        f"B{row['band_lo']}:{row['band_hi']}|"
        f"R{row['u_lo_mod6']}:{row['u_hi_mod6']}"
    )


def collect_sample(binary: Path, q: int, workdir: Path) -> dict[str, Any]:
    c = 6 * q + 5
    m = 8 * c + 2
    cap = max(10_000, 10 * m * m)
    csv_path = workdir / f"r42_carry_atoms_q{q}.csv"
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

    atoms = []
    nonaffine_edge_count = 0
    for (src, dst), members in sorted(groups.items()):
        members = sorted(members, key=lambda row: row["src_a"])
        if affine_coeffs([(member["src_a"], member["qtime"]) for member in members]):
            continue
        nonaffine_edge_count += 1
        for lo, hi in intervals([member["src_a"] for member in members]):
            sub = [member for member in members if lo <= member["src_a"] <= hi]
            coeffs = affine_coeffs([(member["src_a"], member["qtime"]) for member in sub])
            u_lo = lo % c
            u_hi = hi % c
            u_lo_mod6 = u_lo % 6
            u_hi_mod6 = u_hi % 6
            row = {
                "src": src,
                "dst": dst,
                "lo": lo,
                "hi": hi,
                "length": hi - lo + 1,
                "band_lo": lo // c,
                "band_hi": hi // c,
                "u_lo_mod6": u_lo_mod6,
                "u_hi_mod6": u_hi_mod6,
                "j_lo": (u_lo - u_lo_mod6) // 6,
                "j_hi": (u_hi - u_hi_mod6) // 6,
                "qtime_affine": coeffs is not None,
                "qtime_slope": coeffs[0] if coeffs is not None else None,
            }
            row["atom"] = atom_key(row)
            atoms.append(row)
    atom_counts: dict[str, int] = {}
    for row in atoms:
        atom_counts[row["atom"]] = atom_counts.get(row["atom"], 0) + 1
    return {
        "q": q,
        "c": c,
        "m": m,
        "ok": True,
        "nonaffine_edge_count": nonaffine_edge_count,
        "atom_count": len(atom_counts),
        "interval_count": len(atoms),
        "atoms": atoms,
        "atom_counts": atom_counts,
    }


def branch_summary(samples: list[dict[str, Any]], parity: int) -> dict[str, Any]:
    name = "R42-even-q" if parity == 0 else "R42-odd-q"
    selected = [sample for sample in samples if sample.get("ok") and sample["q"] % 2 == parity]
    sample_s = {
        sample["q"]: sample["q"] // 2 if parity == 0 else (sample["q"] - 1) // 2
        for sample in selected
    }
    atom_keys = sorted({row["atom"] for sample in selected for row in sample["atoms"]})
    rows = []
    all_atom_counts_affine = True
    all_j_ranges_affine = True
    missing_atom_sample_count = 0
    for key in atom_keys:
        per_sample = []
        missing_q = []
        for sample in selected:
            rows_for_key = [row for row in sample["atoms"] if row["atom"] == key]
            if not rows_for_key:
                missing_q.append(sample["q"])
                continue
            s = sample_s[sample["q"]]
            per_sample.append((s, sample, rows_for_key))
        if missing_q:
            missing_atom_sample_count += 1
        count_formula = affine_formula(
            [(s, len(rows_for_key)) for s, _, rows_for_key in per_sample], "s"
        )
        min_j_formula = affine_formula(
            [(s, min(row["j_lo"] for row in rows_for_key)) for s, _, rows_for_key in per_sample],
            "s",
        )
        max_j_formula = affine_formula(
            [(s, max(row["j_lo"] for row in rows_for_key)) for s, _, rows_for_key in per_sample],
            "s",
        )
        all_atom_counts_affine = all_atom_counts_affine and count_formula is not None
        all_j_ranges_affine = (
            all_j_ranges_affine
            and min_j_formula is not None
            and max_j_formula is not None
        )
        first_row = per_sample[0][2][0]
        rows.append(
            {
                "atom": key,
                "src": first_row["src"],
                "dst": first_row["dst"],
                "length": first_row["length"],
                "band_lo": first_row["band_lo"],
                "band_hi": first_row["band_hi"],
                "u_lo_mod6": first_row["u_lo_mod6"],
                "u_hi_mod6": first_row["u_hi_mod6"],
                "missing_q_values": missing_q,
                "count_formula": count_formula,
                "min_j_formula": min_j_formula,
                "max_j_formula": max_j_formula,
                "sample_points": [
                    {
                        "q": sample["q"],
                        "s": s,
                        "count": len(rows_for_key),
                        "min_j": min(row["j_lo"] for row in rows_for_key),
                        "max_j": max(row["j_lo"] for row in rows_for_key),
                    }
                    for s, sample, rows_for_key in per_sample
                ],
            }
        )
    return {
        "name": name,
        "parity": parity,
        "sample_q_values": [sample["q"] for sample in selected],
        "sample_s_values": [sample_s[sample["q"]] for sample in selected],
        "atom_key_count": len(atom_keys),
        "missing_atom_sample_count": missing_atom_sample_count,
        "all_atom_counts_affine_in_s": all_atom_counts_affine,
        "all_j_ranges_affine_in_s": all_j_ranges_affine,
        "atoms": rows,
    }


def build_summary(q_values: list[int], binary: Path, compile_binary: bool) -> dict[str, Any]:
    if compile_binary:
        r42.compile_checker(binary)
    with tempfile.TemporaryDirectory(prefix="routeE-r42-carry-atoms-") as tmp:
        samples = [collect_sample(binary, q, Path(tmp)) for q in q_values]
    branches = [branch_summary(samples, 0), branch_summary(samples, 1)]
    return {
        "schema": "routeE_r42_carry_support_atoms_v1",
        "family": "R42, c=6*q+5, m=8*c+2, x=z=c",
        "q_values": q_values,
        "samples": [
            {
                "q": sample.get("q"),
                "c": sample.get("c"),
                "m": sample.get("m"),
                "ok": sample.get("ok"),
                "nonaffine_edge_count": sample.get("nonaffine_edge_count"),
                "atom_count": sample.get("atom_count"),
                "interval_count": sample.get("interval_count"),
            }
            for sample in samples
        ],
        "generic_subbranches": branches,
        "summary": {
            "all_samples_ok": all(sample.get("ok") for sample in samples),
            "nonaffine_edge_counts": {
                str(sample.get("q")): sample.get("nonaffine_edge_count")
                for sample in samples
            },
            "atom_counts": {
                str(sample.get("q")): sample.get("atom_count") for sample in samples
            },
            "interval_counts": {
                str(sample.get("q")): sample.get("interval_count") for sample in samples
            },
            "all_branch_atom_counts_affine": all(
                branch["all_atom_counts_affine_in_s"] for branch in branches
            ),
            "all_branch_j_ranges_affine": all(
                branch["all_j_ranges_affine_in_s"] for branch in branches
            ),
            "missing_atom_sample_counts": {
                branch["name"]: branch["missing_atom_sample_count"] for branch in branches
            },
        },
        "promotion_impact": {
            "closes_residue": False,
            "pointwise_equations_closed": False,
            "no_early_closed": False,
            "diagnosis": (
                "All qtime-missing edge supports are summarized by finite "
                "c-band/u-mod-6 atoms on the sampled witnesses.  This records "
                "candidate states for a clock-carry transducer but does not "
                "prove qtime coefficients or no-early."
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
    print("all_branch_atom_counts_affine", payload["summary"]["all_branch_atom_counts_affine"])
    print("all_branch_j_ranges_affine", payload["summary"]["all_branch_j_ranges_affine"])
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
        print(f"wrote {args.json_out}")


if __name__ == "__main__":
    main()
