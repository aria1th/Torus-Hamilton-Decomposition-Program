#!/usr/bin/env python3
"""Create a compact D7 4+2 bridge snapshot for bundle comparisons."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from zipfile import ZipFile

from search_4plus2_kappa_formulas import (
    kappa_dependency_diagnostics,
    search_dihedral_formulas,
    section_trace_diagnostics,
)
from verify_4plus2_allN_bridge_cert import (
    base_tuple,
    default_bundle_path,
    load_bundle,
    parse_only,
    validate_certificate,
    verify_certificate,
)


def zip_manifest(path: Path) -> list[dict]:
    if not path.exists():
        return []
    with ZipFile(path) as bundle:
        return [
            {
                "name": info.filename,
                "size": info.file_size,
                "compressed_size": info.compress_size,
            }
            for info in sorted(bundle.infolist(), key=lambda item: item.filename)
        ]


def base_word(row: list[int]) -> list[int]:
    return [slot for slot in row if slot < 5]


def row_summary(cert: dict) -> dict:
    return {
        "rows": cert["rows"],
        "base_words": [base_word(row) for row in cert["rows"]],
        "base_word_lengths": [len(base_word(row)) for row in cert["rows"]],
        "extra_counts": [sum(1 for slot in row if slot >= 5) for row in cert["rows"]],
    }


def shifted_zero_mask_code(base: int, m: int) -> int:
    xs = base_tuple(base, m)
    full = (xs[0], xs[1], xs[2], xs[3], (-sum(xs)) % m)
    return sum((1 << i) for i in range(5) if full[(i + 1) % 5] == 0)


def zero_set_k_table_summary(cert: dict) -> dict | None:
    masks = cert.get("masks")
    values = cert.get("kappa_perm_indices_by_mask")
    if masks is None and values is None:
        return None
    if not isinstance(masks, list) or not isinstance(values, list):
        return {"present": True, "valid": False, "error": "masks/table must be lists"}
    if len(masks) != len(values):
        return {"present": True, "valid": False, "error": "masks/table length mismatch"}
    table = {int(mask): int(value) for mask, value in zip(masks, values)}
    mismatches = []
    missing = []
    m = cert["m"]
    for layer, layer_table in enumerate(cert["kappa_perm_indices"]):
        for base, actual in enumerate(layer_table):
            mask = shifted_zero_mask_code(base, m)
            expected = table.get(mask)
            if expected is None:
                if len(missing) < 5:
                    missing.append({"layer": layer, "base": base, "mask": mask})
            elif expected != actual and len(mismatches) < 5:
                mismatches.append(
                    {
                        "layer": layer,
                        "base": base,
                        "mask": mask,
                        "actual": actual,
                        "expected": expected,
                    }
                )
    return {
        "present": True,
        "valid": True,
        "note": cert.get("note"),
        "mask_shift": "mask bit i records full[(i+1) % 5] == 0",
        "table": sorted(table.items()),
        "matches_shifted_zero_mask": not missing and not mismatches,
        "missing_examples": missing,
        "mismatch_examples": mismatches,
    }


def summarize_cert(cert: dict, args: argparse.Namespace) -> dict:
    m = cert.get("m")
    out = {"m": m}
    try:
        validate_certificate(cert)
    except Exception as exc:
        out["valid"] = False
        out["error"] = f"{type(exc).__name__}: {exc}"
        return out
    out["valid"] = True
    out.update(row_summary(cert))
    k_summary = zero_set_k_table_summary(cert)
    if k_summary is not None:
        out["zero_set_K_table"] = k_summary
    out["kappa_diagnostics"] = kappa_dependency_diagnostics(
        m, cert["kappa_perm_indices"], profile=args.diagnostic_profile
    )
    if args.include_full_verify:
        try:
            message, rank_summary = verify_certificate(
                cert, rank_summary=args.include_rank_summary
            )
            out["full_verify"] = {"ok": True, "message": message}
            if rank_summary is not None:
                out["rank_summary"] = rank_summary
        except Exception as exc:
            out["full_verify"] = {
                "ok": False,
                "error": f"{type(exc).__name__}: {exc}",
            }
    if args.include_section_trace:
        try:
            out["section_trace_diagnostics"] = section_trace_diagnostics(cert)
        except Exception as exc:
            out["section_trace_diagnostics"] = {
                "ok": False,
                "error": f"{type(exc).__name__}: {exc}",
            }
    if args.include_dihedral_section:
        out["dihedral_section_search"] = search_dihedral_formulas(
            cert,
            stop_after_first=not args.dihedral_all_hits,
            include_failures=False,
            diagnose_hits=False,
            diagnostic_profile=args.diagnostic_profile,
            section_only=True,
            max_candidates=args.max_dihedral_candidates,
            summarize_failures=args.summarize_failures,
        )
    return out


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--bundle", type=Path, default=default_bundle_path())
    parser.add_argument("--only", help="comma-separated bundled moduli to snapshot")
    parser.add_argument(
        "--cert-json",
        type=Path,
        action="append",
        default=[],
        help="snapshot one or more extracted bridge certificate JSON files",
    )
    parser.add_argument(
        "--diagnostic-profile",
        choices=("basic", "residue", "all"),
        default="all",
        help="kappa dependency diagnostic feature set",
    )
    parser.add_argument("--include-full-verify", action="store_true")
    parser.add_argument("--include-rank-summary", action="store_true")
    parser.add_argument("--include-section-trace", action="store_true")
    parser.add_argument("--include-dihedral-section", action="store_true")
    parser.add_argument("--dihedral-all-hits", action="store_true")
    parser.add_argument("--summarize-failures", action="store_true")
    parser.add_argument("--max-dihedral-candidates", type=int)
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()

    payload = {
        "description": "D7 all-zero-set 4+2 bridge bundle snapshot.",
        "bundle": str(args.bundle),
        "manifest": zip_manifest(args.bundle),
        "certificates": [],
    }
    only = parse_only(args.only)
    if args.cert_json:
        certs = []
        for path in args.cert_json:
            cert = json.loads(path.read_text())
            if only is None or cert.get("m") in only:
                certs.append(cert)
    else:
        try:
            certs = load_bundle(args.bundle, only)
        except Exception as exc:
            payload["load_error"] = f"{type(exc).__name__}: {exc}"
            certs = []
    for cert in certs:
        payload["certificates"].append(summarize_cert(cert, args))

    text = json.dumps(payload, indent=2, sort_keys=True)
    if args.json_out is None:
        print(text)
    else:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(text + "\n")
        print(f"wrote {args.json_out}")


if __name__ == "__main__":
    main()
