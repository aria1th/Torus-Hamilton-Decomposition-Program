#!/usr/bin/env python3
"""Verify D5 Route-E small-seam rank certificates.

The Lean target `RouteEThetaRankedPiecewiseTranslationCertificate` expects a
one-dimensional seam return, interval translation blocks, and a bijective rank
whose value increases by one under the seam return.  This script exports and
verifies that proof-facing data for the finite `SMALL_SEAM_CASES` table.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Dict, Iterable, List, Tuple

import verify_d5_even_routeE as route_e

ParamMap = Dict[int, int]
TimeMap = Dict[int, int]
CountVec = Tuple[int, int, int, int, int]


def compute_first_return(
    m: int, slot: int, counts: CountVec
) -> tuple[ParamMap, TimeMap, bool, list[int]]:
    seam_port = (slot + 2) % 5
    first_return: ParamMap = {}
    return_times: TimeMap = {}
    start_ok = True
    no_return: list[int] = []
    max_steps = m**4 + 5
    for a in range(1, m):
        w = route_e.theta_state(m, slot, a)
        if route_e.lam(route_e.PERT, route_e.shifted_zero_mask(w), slot) != seam_port:
            start_ok = False
        for time in range(1, max_steps + 1):
            w = route_e.one_e_return_step_with_slot(m, slot, counts, w)
            b = route_e.theta_param(m, slot, w)
            if b is not None:
                first_return[a] = b
                return_times[a] = time
                break
        else:
            no_return.append(a)
            if len(no_return) > 10:
                break
    return first_return, return_times, start_ok, no_return


def rank_from_orbit(m: int, mapping: ParamMap, start: int = 1) -> tuple[list[int], list[int]]:
    n = m - 1
    rank_by_param = [-1] * n
    inv_rank: list[int] = []
    seen: set[int] = set()
    x = start
    for rank in range(n):
        if x in seen or not (1 <= x < m):
            raise ValueError(f"orbit left domain or repeated early at {x}")
        seen.add(x)
        rank_by_param[x - 1] = rank
        inv_rank.append(x)
        x = mapping[x]
    if x != start or len(seen) != n or any(rank < 0 for rank in rank_by_param):
        raise ValueError("first-return map is not one full seam cycle")
    return rank_by_param, inv_rank


def build_case_cert(m: int, slot: int, counts: CountVec) -> dict:
    mapping, times, start_ok, no_return = compute_first_return(m, slot, counts)
    if not start_ok or no_return:
        raise ValueError(f"bad first-return data for m={m}: start_ok={start_ok} no_return={no_return}")
    rank_by_param, inv_rank = rank_from_orbit(m, mapping)
    blocks = route_e.translation_blocks(m, mapping)
    return {
        "m": m,
        "slot": slot,
        "counts": list(counts),
        "seam_size": m - 1,
        "rank_start": 1,
        "rank_by_param": rank_by_param,
        "inv_rank": inv_rank,
        "translation_blocks": blocks,
        "return_time_sum": sum(times.values()),
        "expected_return_time_sum": m**4,
    }


def build_cert(moduli: Iterable[int] | None = None) -> dict:
    chosen = sorted(route_e.SMALL_SEAM_CASES if moduli is None else moduli)
    cases = []
    for m in chosen:
        data = route_e.SMALL_SEAM_CASES[m]
        cases.append(build_case_cert(m, data["slot"], data["counts"]))
    return {
        "schema": "d5_routeE_small_seam_rank_certs_v1",
        "source": "verify_d5_even_routeE.SMALL_SEAM_CASES",
        "case_count": len(cases),
        "cases": cases,
    }


def verify_blocks(m: int, mapping: ParamMap, blocks: list[dict]) -> list[str]:
    errors: list[str] = []
    covered: list[int] = []
    for idx, block in enumerate(blocks):
        start = block.get("start")
        end = block.get("end")
        delta = block.get("delta")
        length = block.get("length")
        if not isinstance(start, int) or not isinstance(end, int) or not isinstance(delta, int):
            errors.append(f"block {idx}: malformed block endpoints or delta")
            continue
        if start < 1 or end >= m or start > end:
            errors.append(f"block {idx}: invalid interval [{start},{end}] for m={m}")
            continue
        if length != end - start + 1:
            errors.append(f"block {idx}: bad length")
        for a in range(start, end + 1):
            covered.append(a)
            if mapping[a] != (a + delta) % m:
                errors.append(f"block {idx}: translation mismatch at a={a}")
                break
    if covered != list(range(1, m)):
        errors.append("blocks do not form a disjoint ordered cover of 1..m-1")
    if blocks != route_e.translation_blocks(m, mapping):
        errors.append("blocks are not the maximal translation blocks")
    return errors


def verify_case(cert: dict) -> dict:
    m = int(cert["m"])
    if m not in route_e.SMALL_SEAM_CASES:
        return {"m": m, "ok": False, "errors": ["modulus not present in SMALL_SEAM_CASES"]}
    expected = route_e.SMALL_SEAM_CASES[m]
    errors: list[str] = []
    slot = int(cert["slot"])
    counts = tuple(int(x) for x in cert["counts"])
    if slot != expected["slot"] or counts != tuple(expected["counts"]):
        errors.append("slot/counts do not match SMALL_SEAM_CASES")
    if sum(counts) != m - 1:
        errors.append("counts do not sum to m-1")

    mapping, times, start_ok, no_return = compute_first_return(m, slot, counts)
    if not start_ok:
        errors.append("theta seam start port check failed")
    if no_return:
        errors.append(f"missing first returns: {no_return[:5]}")

    n = m - 1
    rank_by_param = [int(x) for x in cert["rank_by_param"]]
    inv_rank = [int(x) for x in cert["inv_rank"]]
    if len(rank_by_param) != n or len(inv_rank) != n:
        errors.append("rank arrays have wrong length")
    elif sorted(rank_by_param) != list(range(n)) or sorted(inv_rank) != list(range(1, m)):
        errors.append("rank arrays are not bijective over seam/rank domains")
    else:
        for rank, a in enumerate(inv_rank):
            if rank_by_param[a - 1] != rank:
                errors.append(f"rank/inverse mismatch at rank={rank}")
                break
        for a in range(1, m):
            b = mapping[a]
            got = rank_by_param[b - 1]
            want = (rank_by_param[a - 1] + 1) % n
            if got != want:
                errors.append(f"rank step mismatch at a={a}: got {got}, want {want}")
                break

    return_sum = sum(times.values())
    if cert.get("return_time_sum") != return_sum:
        errors.append("return_time_sum does not match recomputed value")
    if return_sum != m**4 or cert.get("expected_return_time_sum") != m**4:
        errors.append("return-time sum is not m^4")

    errors.extend(verify_blocks(m, mapping, cert.get("translation_blocks", [])))
    return {
        "m": m,
        "slot": slot,
        "seam_size": n,
        "block_count": len(cert.get("translation_blocks", [])),
        "return_time_sum": return_sum,
        "ok": not errors,
        "errors": errors,
    }


def verify_cert(payload: dict) -> dict:
    cases = payload.get("cases", [])
    results = [verify_case(case) for case in cases]
    moduli = [result["m"] for result in results]
    missing = sorted(set(route_e.SMALL_SEAM_CASES) - set(moduli))
    extra = sorted(set(moduli) - set(route_e.SMALL_SEAM_CASES))
    return {
        "schema": payload.get("schema"),
        "case_count": len(results),
        "moduli": moduli,
        "missing_moduli": missing,
        "extra_moduli": extra,
        "all_ok": all(result["ok"] for result in results) and not missing and not extra,
        "results": results,
    }


def parse_moduli(text: str | None) -> list[int] | None:
    if text is None or text == "all":
        return None
    return [int(part) for part in text.split(",") if part.strip()]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--cert", type=Path, help="existing rank certificate JSON to verify")
    parser.add_argument("--write-cert", type=Path, help="write generated certificate JSON")
    parser.add_argument("--moduli", default="all", help="comma-separated moduli for generation, or all")
    parser.add_argument("--json-out", type=Path, help="write verification summary JSON")
    args = parser.parse_args()

    if args.cert is not None:
        payload = json.loads(args.cert.read_text())
    else:
        payload = build_cert(parse_moduli(args.moduli))

    if args.write_cert is not None:
        args.write_cert.write_text(json.dumps(payload, indent=2) + "\n")

    summary = verify_cert(payload)
    print(
        "cases",
        summary["case_count"],
        "all_ok",
        summary["all_ok"],
        "missing",
        summary["missing_moduli"],
        "extra",
        summary["extra_moduli"],
    )
    for result in summary["results"]:
        if not result["ok"]:
            print("bad", result["m"], result["errors"][:3])
    if args.json_out is not None:
        args.json_out.write_text(json.dumps(summary, indent=2) + "\n")
    if not summary["all_ok"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
