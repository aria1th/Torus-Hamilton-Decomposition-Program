#!/usr/bin/env python3
"""Parallel probe for D5 even Route-E symmetric direct packets.

This discovery driver tests packets of the form

    nu = (x, m - 1 - 2*x, 0, x, 0)

against `fast_d5_routeE_small_seam_verify.cpp`.  It is deliberately a
lightweight evidence generator: successful hits should still be promoted to
paper-facing modular criteria or exact Lean/script checks before being treated
as proof.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
from tempfile import gettempdir


REPO = Path(__file__).resolve().parents[1]
VERIFIER_CPP = REPO / "scripts" / "fast_d5_routeE_small_seam_verify.cpp"
DEFAULT_BIN = Path(gettempdir()) / "fast_d5_routeE_small_seam_verify"
FIRST_LINE_RE = re.compile(
    r"m (?P<m>\d+) slot (?P<slot>\d+) j (?P<j>\d+) counts (?P<counts>(?:-?\d+ ?)+) "
    r"start_ok (?P<start_ok>[01]) cycles(?P<cycles>(?: \d+)*) "
    r"sum (?P<time_sum>\d+) m4 (?P<m4>\d+) ok (?P<ok>[01])"
)


def parse_ints(text: str) -> list[int]:
    text = text.strip()
    if not text:
        return []
    if ":" in text:
        parts = [int(x) for x in text.split(":")]
        if len(parts) == 2:
            start, stop = parts
            step = 1
        elif len(parts) == 3:
            start, stop, step = parts
        else:
            raise ValueError("range syntax must be start:stop[:step]")
        return list(range(start, stop + 1, step))
    return [int(part) for part in text.split(",") if part.strip()]


def compile_binary(binary: Path) -> None:
    subprocess.run(
        ["g++", "-O3", "-std=c++17", str(VERIFIER_CPP), "-o", str(binary)],
        check=True,
        cwd=REPO,
    )


def parse_verifier_output(stdout: str) -> dict:
    first = stdout.splitlines()[0] if stdout.splitlines() else ""
    match = FIRST_LINE_RE.fullmatch(first.strip())
    if not match:
        return {"parsed": False, "first_line": first}
    counts = [int(x) for x in match.group("counts").split()]
    cycles = [int(x) for x in match.group("cycles").split()]
    return {
        "parsed": True,
        "m": int(match.group("m")),
        "slot": int(match.group("slot")),
        "j": int(match.group("j")),
        "counts": counts,
        "start_ok": match.group("start_ok") == "1",
        "cycles": cycles,
        "time_sum": int(match.group("time_sum")),
        "m4": int(match.group("m4")),
        "ok": match.group("ok") == "1",
    }


def run_candidate(binary: Path, m: int, x: int, timeout: float) -> dict:
    middle = m - 1 - 2 * x
    if x <= 0 or middle < 0:
        return {
            "m": m,
            "x": x,
            "skipped": True,
            "reason": "invalid packet",
        }
    cmd = [str(binary), str(m), "0", str(x), str(middle), "0", str(x), "0"]
    try:
        proc = subprocess.run(
            cmd,
            cwd=REPO,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=timeout,
            check=False,
        )
    except subprocess.TimeoutExpired:
        return {"m": m, "x": x, "timeout": True, "timeout_seconds": timeout}
    parsed = parse_verifier_output(proc.stdout)
    return {
        "m": m,
        "x": x,
        "returncode": proc.returncode,
        "result": parsed,
        "stderr_tail": proc.stderr.strip().splitlines()[-3:],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--moduli", required=True, help="comma list or start:stop[:step]")
    parser.add_argument("--x-values", default="1:31:2", help="comma list or start:stop[:step]")
    parser.add_argument("--timeout", type=float, default=12.0)
    parser.add_argument("--jobs", type=int, default=4)
    parser.add_argument("--binary", type=Path, default=DEFAULT_BIN)
    parser.add_argument("--no-compile", action="store_true")
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()

    if not args.no_compile:
        compile_binary(args.binary)

    moduli = parse_ints(args.moduli)
    x_values = parse_ints(args.x_values)
    tasks = [(m, x) for m in moduli for x in x_values]
    results = []
    hits: dict[int, list[int]] = {}

    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        future_map = {
            pool.submit(run_candidate, args.binary, m, x, args.timeout): (m, x)
            for m, x in tasks
        }
        for future in as_completed(future_map):
            result = future.result()
            results.append(result)
            parsed = result.get("result", {})
            if parsed.get("ok"):
                hits.setdefault(result["m"], []).append(result["x"])
                print("HIT", result["m"], result["x"], parsed.get("cycles"))

    for xs in hits.values():
        xs.sort()
    results.sort(key=lambda item: (item["m"], item["x"]))
    payload = {
        "schema": "d5_routeE_symmetric_packet_probe_v1",
        "moduli": moduli,
        "x_values": x_values,
        "timeout_seconds": args.timeout,
        "hits": {str(k): v for k, v in sorted(hits.items())},
        "results": results,
    }
    print("SUMMARY")
    for m in sorted(hits):
        print(m, hits[m])
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")


if __name__ == "__main__":
    main()
