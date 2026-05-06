#!/usr/bin/env python3
"""Parallel C++ discovery driver for D5 even Route-E small-seam branches.

This is a discovery tool, not a proof checker.  It compiles
`fast_d5_routeE_small_seam_search.cpp`, runs it over selected even moduli and
support patterns, and stores only compact hit summaries.  Use a positive
`--cap-m3-factor` for broad discovery, then rerun interesting candidates with
the one-candidate verifier or `--cap-m3-factor 0` for exact confirmation.
"""

from __future__ import annotations

import argparse
import csv
import json
import subprocess
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
from tempfile import gettempdir


REPO = Path(__file__).resolve().parents[1]
CPP = REPO / "scripts" / "fast_d5_routeE_small_seam_search.cpp"
DEFAULT_BIN = Path(gettempdir()) / "fast_d5_routeE_small_seam_search"


def parse_moduli(text: str) -> list[int]:
    text = text.strip()
    if ":" in text:
        parts = [int(x) for x in text.split(":")]
        if len(parts) == 2:
            start, stop = parts
            step = 2
        elif len(parts) == 3:
            start, stop, step = parts
        else:
            raise ValueError("--moduli range must be start:stop[:step]")
        return list(range(start, stop + 1, step))
    return [int(part) for part in text.split(",") if part.strip()]


def parse_patterns(text: str) -> list[str]:
    return [part.strip() for part in text.split(";") if part.strip()]


def compile_binary(binary: Path) -> None:
    cmd = ["g++", "-O3", "-std=c++17", str(CPP), "-o", str(binary)]
    subprocess.run(cmd, check=True, cwd=REPO)


def parse_hits(stdout: str) -> list[dict]:
    lines = [line for line in stdout.splitlines() if line.strip()]
    if len(lines) <= 1:
        return []
    reader = csv.DictReader(lines)
    hits = []
    for row in reader:
        counts = tuple(int(x) for x in row["counts"].split())
        hits.append(
            {
                "checked_at_hit": int(row["checked"]),
                "counts": counts,
                "cycles": [int(x) for x in row["cycles"].split()],
                "time_sum": int(row["time_sum"]),
                "m4": int(row["m4"]),
                "block_count": int(row["block_count"]),
                "max_block": int(row["max_block"]),
                "blocks_prefix": row["blocks_prefix"],
            }
        )
    return hits


def parse_summary(stderr: str) -> dict:
    out: dict[str, int | str] = {}
    for token in stderr.strip().split():
        if "=" not in token:
            continue
        key, value = token.split("=", 1)
        try:
            out[key] = int(value)
        except ValueError:
            out[key] = value
    return out


def run_task(
    binary: Path,
    m: int,
    pattern: str,
    hit_limit: int,
    cap_m3_factor: float,
    candidate_limit: int,
    timeout: float,
) -> dict:
    cap = 0 if cap_m3_factor == 0 else int(cap_m3_factor * (m**3))
    cmd = [
        str(binary),
        str(m),
        pattern,
        str(hit_limit),
        str(cap),
        str(candidate_limit),
    ]
    try:
        proc = subprocess.run(
            cmd,
            cwd=REPO,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
            timeout=None if timeout <= 0 else timeout,
        )
    except subprocess.TimeoutExpired as exc:
        stdout = exc.stdout or ""
        stderr = exc.stderr or ""
        if isinstance(stdout, bytes):
            stdout = stdout.decode(errors="replace")
        if isinstance(stderr, bytes):
            stderr = stderr.decode(errors="replace")
        return {
            "m": m,
            "pattern": pattern,
            "cap_steps": cap,
            "candidate_limit": candidate_limit,
            "timeout": True,
            "timeout_seconds": timeout,
            "returncode": None,
            "summary": parse_summary(stderr),
            "hits": parse_hits(stdout),
            "stderr_tail": stderr.strip().splitlines()[-5:],
        }
    return {
        "m": m,
        "pattern": pattern,
        "cap_steps": cap,
        "candidate_limit": candidate_limit,
        "timeout": False,
        "timeout_seconds": timeout,
        "returncode": proc.returncode,
        "summary": parse_summary(proc.stderr),
        "hits": parse_hits(proc.stdout) if proc.returncode == 0 else [],
        "stderr_tail": proc.stderr.strip().splitlines()[-5:],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--moduli", required=True, help="comma list or start:stop[:step]")
    parser.add_argument(
        "--patterns",
        default="0,1,3;0,3,4;1,2,3;1,3,4;0,1,4;0,2,3;2,3,4",
        help="semicolon-separated support patterns",
    )
    parser.add_argument("--hit-limit", type=int, default=5)
    parser.add_argument("--candidate-limit", type=int, default=20000)
    parser.add_argument(
        "--cap-m3-factor",
        type=float,
        default=4.0,
        help="per seam-point cap = factor*m^3; use 0 for exact unbounded-to-m^4 search",
    )
    parser.add_argument("--jobs", type=int, default=4)
    parser.add_argument(
        "--timeout",
        type=float,
        default=0.0,
        help="per C++ subprocess timeout in seconds; 0 means no timeout",
    )
    parser.add_argument("--binary", type=Path, default=DEFAULT_BIN)
    parser.add_argument("--no-compile", action="store_true")
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()

    if not args.no_compile:
        compile_binary(args.binary)

    moduli = parse_moduli(args.moduli)
    patterns = parse_patterns(args.patterns)
    tasks = [(m, pattern) for m in moduli for pattern in patterns]
    results = []
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        future_map = {
            pool.submit(
                run_task,
                args.binary,
                m,
                pattern,
                args.hit_limit,
                args.cap_m3_factor,
                args.candidate_limit,
                args.timeout,
            ): (m, pattern)
            for m, pattern in tasks
        }
        for future in as_completed(future_map):
            result = future.result()
            results.append(result)
            print(
                "m",
                result["m"],
                "pattern",
                result["pattern"],
                "hits",
                len(result["hits"]),
                "checked",
                result["summary"].get("checked"),
                "timeout",
                result.get("timeout"),
            )

    results.sort(key=lambda x: (x["m"], x["pattern"]))
    payload = {
        "schema": "d5_routeE_cpp_residue_branch_search_v1",
        "moduli": moduli,
        "patterns": patterns,
        "hit_limit": args.hit_limit,
        "candidate_limit": args.candidate_limit,
        "cap_m3_factor": args.cap_m3_factor,
        "timeout_seconds": args.timeout,
        "results": results,
    }
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")


if __name__ == "__main__":
    main()
