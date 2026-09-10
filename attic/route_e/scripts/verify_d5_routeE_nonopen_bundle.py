#!/usr/bin/env python3
"""Check the D5 Route-E non-open small-seam bundle against repo artifacts.

The source bundle `d5_even_routeE_nonopen_small_seam_v0_4.zip` contains a TSV
schedule table and a standalone verifier transcript.  This script treats those
files as audit inputs: it compares the bundle table to the repo's embedded
`SMALL_SEAM_CASES`, parses the transcript, and recomputes the small-seam
criterion with `verify_d5_even_routeE.py`.
"""

from __future__ import annotations

import argparse
import json
import zipfile
from pathlib import Path
from typing import Dict, Iterable, Tuple

import verify_d5_even_routeE as route_e

CountVec = Tuple[int, int, int, int, int]
CaseTable = Dict[int, tuple[int, CountVec]]

CASES_SUFFIX = "outputs/d5_even_routeE_small_seam_extended_cases.tsv"
VERIFY_SUFFIX = "outputs/d5_even_routeE_small_seam_extended_verify.txt"


def read_bundle_text(bundle: Path, suffix: str) -> str:
    if bundle.is_file() and zipfile.is_zipfile(bundle):
        with zipfile.ZipFile(bundle) as zf:
            matches = [name for name in zf.namelist() if name.endswith(suffix)]
            if len(matches) != 1:
                raise ValueError(f"expected one {suffix} in zip, found {matches}")
            return zf.read(matches[0]).decode()
    if bundle.is_dir():
        matches = [path for path in bundle.rglob(Path(suffix).name) if str(path).endswith(suffix)]
        if len(matches) != 1:
            raise ValueError(f"expected one {suffix} in directory, found {matches}")
        return matches[0].read_text()
    raise ValueError(f"bundle must be a zip file or directory: {bundle}")


def parse_cases_tsv(text: str) -> CaseTable:
    cases: CaseTable = {}
    for line_number, raw in enumerate(text.splitlines(), start=1):
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        parts = line.split()
        if len(parts) != 7:
            raise ValueError(f"bad TSV line {line_number}: {raw!r}")
        m = int(parts[0])
        slot = int(parts[1])
        counts = tuple(int(x) for x in parts[2:7])
        if len(counts) != 5:
            raise ValueError(f"bad count vector on line {line_number}")
        cases[m] = (slot, counts)  # type: ignore[assignment]
    return cases


def parse_report_line(line: str) -> dict | None:
    parts = line.split()
    if not parts or parts[0] != "m":
        return None
    try:
        m = int(parts[1])
        slot = int(parts[3])
        j = int(parts[5])
        counts = tuple(int(x) for x in parts[7:12])
        start_ok = parts[13] == "1"
        sum_idx = parts.index("sum")
        cycles = [int(x) for x in parts[15:sum_idx]]
        return_sum = int(parts[sum_idx + 1])
        m4 = int(parts[sum_idx + 3])
        ok = parts[sum_idx + 5] == "1"
    except (IndexError, ValueError) as exc:
        raise ValueError(f"could not parse verifier report line: {line!r}") from exc
    return {
        "m": m,
        "slot": slot,
        "j": j,
        "counts": counts,
        "start_ok": start_ok,
        "cycles": cycles,
        "return_time_sum": return_sum,
        "expected_return_time_sum": m4,
        "ok": ok,
    }


def parse_verify_report(text: str) -> dict[int, dict]:
    reports: dict[int, dict] = {}
    for raw in text.splitlines():
        parsed = parse_report_line(raw.strip())
        if parsed is not None:
            reports[parsed["m"]] = parsed
    return reports


def repo_cases() -> CaseTable:
    return {
        m: (int(data["slot"]), tuple(int(x) for x in data["counts"]))
        for m, data in route_e.SMALL_SEAM_CASES.items()
    }


def compare_tables(left: CaseTable, right: CaseTable) -> list[str]:
    errors: list[str] = []
    left_moduli = set(left)
    right_moduli = set(right)
    for m in sorted(left_moduli - right_moduli):
        errors.append(f"extra modulus {m}")
    for m in sorted(right_moduli - left_moduli):
        errors.append(f"missing modulus {m}")
    for m in sorted(left_moduli & right_moduli):
        if left[m] != right[m]:
            errors.append(f"m={m}: got {left[m]}, expected {right[m]}")
    return errors


def verify_report_against_cases(reports: dict[int, dict], cases: CaseTable) -> list[str]:
    errors: list[str] = []
    for m in sorted(set(reports) - set(cases)):
        errors.append(f"report has extra modulus {m}")
    for m in sorted(set(cases) - set(reports)):
        errors.append(f"report missing modulus {m}")
    for m in sorted(set(reports) & set(cases)):
        slot, counts = cases[m]
        report = reports[m]
        if report["slot"] != slot or report["counts"] != counts:
            errors.append(f"m={m}: report slot/counts mismatch")
        if report["j"] != (slot + 2) % 5:
            errors.append(f"m={m}: report seam port is not slot+2")
        if not report["start_ok"]:
            errors.append(f"m={m}: report start_ok is false")
        if report["cycles"] != [m - 1]:
            errors.append(f"m={m}: report cycles are not [{m - 1}]")
        if report["return_time_sum"] != m**4 or report["expected_return_time_sum"] != m**4:
            errors.append(f"m={m}: report return-time sum is not m^4")
        if not report["ok"]:
            errors.append(f"m={m}: report ok flag is false")
    return errors


def recompute_cases(cases: CaseTable) -> list[dict]:
    results = []
    for m, (slot, counts) in sorted(cases.items()):
        result = route_e.verify_small_seam_case(m, slot, counts)
        results.append(
            {
                "m": m,
                "slot": slot,
                "seam_size": result["seam_size"],
                "cycle_lengths": result["cycle_lengths"],
                "return_time_sum": result["return_time_sum"],
                "expected_return_time_sum": result["expected_return_time_sum"],
                "translation_block_count": result["translation_block_count"],
                "ok": result["ok"],
            }
        )
    return results


def check_recomputed(results: Iterable[dict]) -> list[str]:
    errors: list[str] = []
    for result in results:
        m = result["m"]
        if not result["ok"]:
            errors.append(f"m={m}: recomputed small-seam check failed")
        if result["cycle_lengths"] != [m - 1]:
            errors.append(f"m={m}: recomputed seam map is not one cycle")
        if result["return_time_sum"] != m**4:
            errors.append(f"m={m}: recomputed return-time sum is not m^4")
    return errors


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("bundle", type=Path, help="bundle zip or extracted directory")
    parser.add_argument("--json-out", type=Path, help="write summary JSON")
    args = parser.parse_args()

    cases = parse_cases_tsv(read_bundle_text(args.bundle, CASES_SUFFIX))
    reports = parse_verify_report(read_bundle_text(args.bundle, VERIFY_SUFFIX))
    repo = repo_cases()
    recomputed = recompute_cases(cases)

    table_errors = compare_tables(cases, repo)
    report_errors = verify_report_against_cases(reports, cases)
    recompute_errors = check_recomputed(recomputed)
    all_ok = not table_errors and not report_errors and not recompute_errors

    summary = {
        "schema": "d5_routeE_nonopen_bundle_check_v1",
        "bundle": str(args.bundle),
        "case_count": len(cases),
        "moduli": sorted(cases),
        "tsv_matches_repo": not table_errors,
        "report_matches_tsv": not report_errors,
        "python_recompute_all_ok": not recompute_errors,
        "all_ok": all_ok,
        "table_errors": table_errors,
        "report_errors": report_errors,
        "recompute_errors": recompute_errors,
        "recomputed": recomputed,
    }

    print(
        "cases",
        summary["case_count"],
        "tsv_matches_repo",
        summary["tsv_matches_repo"],
        "report_matches_tsv",
        summary["report_matches_tsv"],
        "python_recompute_all_ok",
        summary["python_recompute_all_ok"],
        "all_ok",
        summary["all_ok"],
    )
    if args.json_out is not None:
        args.json_out.write_text(json.dumps(summary, indent=2) + "\n")
    if not all_ok:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
