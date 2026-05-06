#!/usr/bin/env python3
"""Verify the compact R42 all-pair time-fit summary."""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_CERT = ROOT / "certs" / "routeE_r42_allpair_time_fit_summary.json"
LABELS = ["Z", "01", "02", "03", "04", "12", "13", "14", "23", "24", "34"]


def eval_coeffs(coeffs: list[str], q: int) -> int:
    value = sum(Fraction(coeff) * Fraction(q) ** power for power, coeff in enumerate(coeffs))
    if value.denominator != 1:
        raise ValueError(f"nonintegral polynomial value at q={q}: {value}")
    return value.numerator


def expected_m4_coeffs() -> list[str]:
    # (48*q + 42)^4, coefficients in ascending q-power order.
    return [
        str(42**4),
        str(4 * 42**3 * 48),
        str(6 * 42**2 * 48**2),
        str(4 * 42 * 48**3),
        str(48**4),
    ]


def check_fit_table(
    samples: list[dict[str, Any]], fits: dict[str, Any], sample_key: str
) -> list[dict[str, Any]]:
    bad = []
    for sample in samples:
        q = int(sample["q"])
        values = sample.get(sample_key, {})
        for label in LABELS:
            fit = fits.get(label, {})
            coeffs = fit.get("coefficients_ascending", [])
            if fit.get("status") != "polynomial_fit" or not coeffs:
                bad.append({"check": "missing_fit", "sample_key": sample_key, "label": label})
                continue
            expected = eval_coeffs(coeffs, q)
            actual = values.get(label)
            if expected != actual:
                bad.append(
                    {
                        "check": "fit_value",
                        "sample_key": sample_key,
                        "label": label,
                        "q": q,
                        "expected": expected,
                        "actual": actual,
                    }
                )
    return bad


def build_verification(cert: Path) -> dict[str, Any]:
    data = json.loads(cert.read_text())
    samples = data.get("samples", [])
    fits = data.get("fits", {})
    bad = []
    if data.get("schema") != "routeE_r42_allpair_time_fit_summary_v1":
        bad.append({"check": "schema", "actual": data.get("schema")})
    expected_total_coeffs = expected_m4_coeffs()
    total_fit = fits.get("time_total", {})
    if total_fit.get("coefficients_ascending") != expected_total_coeffs:
        bad.append(
            {
                "check": "time_total_coefficients",
                "expected": expected_total_coeffs,
                "actual": total_fit.get("coefficients_ascending"),
            }
        )
    for sample in samples:
        q = int(sample["q"])
        if sample.get("time_total") != sample.get("m4"):
            bad.append({"check": "sample_time_total", "q": q})
        if sample.get("time_total") != eval_coeffs(expected_total_coeffs, q):
            bad.append({"check": "sample_time_total_formula", "q": q})
        if sum(sample.get("label_count", {}).values()) != sample.get("allpair_nodes"):
            bad.append({"check": "label_count_total", "q": q})
        if sum(sample.get("dst_count", {}).values()) != sample.get("allpair_nodes"):
            bad.append({"check": "dst_count_total", "q": q})
        if sum(sample.get("label_time", {}).values()) != sample.get("time_total"):
            bad.append({"check": "label_time_total", "q": q})
        if sum(sample.get("dst_time", {}).values()) != sample.get("time_total"):
            bad.append({"check": "dst_time_total", "q": q})
    for key in ["label_count", "label_time", "dst_count", "dst_time"]:
        bad.extend(check_fit_table(samples, fits.get(key, {}), key))
    return {
        "schema": "routeE_r42_allpair_time_fit_verification_v1",
        "source": str(cert),
        "ok": not bad,
        "bad_examples": bad[:20],
        "summary": {
            "sample_q_values": [sample.get("q") for sample in samples],
            "time_total_is_m4_polynomial": total_fit.get("coefficients_ascending")
            == expected_total_coeffs,
            "label_count_fits_verified": not check_fit_table(samples, fits.get("label_count", {}), "label_count"),
            "label_time_fits_verified": not check_fit_table(samples, fits.get("label_time", {}), "label_time"),
            "dst_count_fits_verified": not check_fit_table(samples, fits.get("dst_count", {}), "dst_count"),
            "dst_time_fits_verified": not check_fit_table(samples, fits.get("dst_time", {}), "dst_time"),
        },
        "warning": (
            "This verifies the committed time-fit artifact. It does not "
            "regenerate CSV witnesses and does not prove no-early returns."
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--cert", type=Path, default=DEFAULT_CERT)
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()

    payload = build_verification(args.cert)
    print("schema", payload["schema"])
    print("ok", payload["ok"])
    print("sample_q_values", payload["summary"]["sample_q_values"])
    print("time_total_is_m4_polynomial", payload["summary"]["time_total_is_m4_polynomial"])
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
        print(f"wrote {args.json_out}")
    if not payload["ok"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
