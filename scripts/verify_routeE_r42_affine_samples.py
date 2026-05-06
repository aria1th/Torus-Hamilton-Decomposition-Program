#!/usr/bin/env python3
"""Verify the R42 affine Route-E sample family with the all-pair checker.

This is a sample verifier, not a symbolic branch proof.  It recompiles the
compact C++ all-pair checker and verifies the three portfolio samples for

    m = 48*q + 42,  x = z = 6*q + 5,  q = 0, 1, 2.

The output is intentionally compact so it can be committed as evidence without
preserving raw traces.
"""

from __future__ import annotations

import argparse
import json
import subprocess
from pathlib import Path
from tempfile import gettempdir


REPO = Path(__file__).resolve().parents[1]
CPP = REPO / "scripts" / "routeE_allpair_cpp_v1_2.cpp"
DEFAULT_BIN = Path(gettempdir()) / "routeE_allpair_cpp_v1_2"
DEFAULT_SAMPLES = [0, 1, 2]


def compile_checker(binary: Path) -> None:
    subprocess.run(
        ["g++", "-O3", "-std=c++17", str(CPP), "-o", str(binary)],
        cwd=REPO,
        check=True,
    )


def check_sample(binary: Path, q: int) -> dict:
    m = 48 * q + 42
    x = 6 * q + 5
    z = x
    cap_events = max(10_000, 10 * m * m)
    proc = subprocess.run(
        [str(binary), "check", str(m), str(x), str(z), str(cap_events)],
        cwd=REPO,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    try:
        payload = json.loads(proc.stdout)
    except json.JSONDecodeError:
        payload = {
            "parse_error": True,
            "stdout_head": proc.stdout.splitlines()[:6],
        }
    return {
        "q": q,
        "m": m,
        "x": x,
        "z": z,
        "cap_events": cap_events,
        "returncode": proc.returncode,
        "checker": payload,
        "stderr_tail": proc.stderr.strip().splitlines()[-3:],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--binary", type=Path, default=DEFAULT_BIN)
    parser.add_argument("--no-compile", action="store_true")
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()

    if not args.no_compile:
        compile_checker(args.binary)

    samples = [check_sample(args.binary, q) for q in DEFAULT_SAMPLES]
    for sample in samples:
        checker = sample["checker"]
        sample["passed"] = (
            sample["returncode"] == 0
            and checker.get("count_admissible") is True
            and checker.get("unit_pair") is True
            and checker.get("ok_returns") is True
            and checker.get("sum_ok") is True
            and checker.get("single_cycle") is True
        )

    payload = {
        "schema": "routeE_r42_affine_samples_verification_v1",
        "branch": "R42",
        "status": "sample_verified_not_symbolic_proof",
        "family": "m = 48*q + 42, x = z = 6*q + 5",
        "source_checker": str(CPP.relative_to(REPO)),
        "all_passed": all(sample["passed"] for sample in samples),
        "samples": samples,
        "remaining_symbolic_obligations": [
            "closed branch formula for all q >= 0",
            "RF1/RF2 one-layer validity or adapter-level derivation",
            "product_t Lambda_t = -1 sign proof",
            "pointwise first-return equations",
            "no-early/minimality proof",
            "quotient or splice one-cycle proof",
            "sum tau = m^4 time identity",
            "Lean-facing theorem endpoint",
        ],
    }
    text = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    print(text, end="")
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(text)

    if not payload["all_passed"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
