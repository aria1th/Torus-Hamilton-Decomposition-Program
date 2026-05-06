#!/usr/bin/env python3
"""Verify switch-count polynomials for known one-Lambda_E D5 witnesses.

For the embedded even witnesses with m >= 6, the exported layer table has one
state-dependent Lambda_E defect layer.  This script checks that its modal row,
number of distinct local rows, and adjacent-switch rank totals match the
polynomials observed in the proof-discovery run.

This does not prove the Route-E branch.  It records a stable finite pattern
that a future symbolic affine-seam proof should explain.
"""

from __future__ import annotations

import argparse
from collections import Counter

import analyze_d5_routeE_layer_switches as switches
import export_d5_even_routeE_layers as exporter


MODAL_ROW = (4, 3, 2, 1, 0)
MODAL_ROW_ROTATIONS = {
    tuple((value + shift) % 5 for value in MODAL_ROW) for shift in range(5)
}


def expected_modal(m: int) -> int:
    return m**4 - 5 * m**3 + 10 * m**2 - 10 * m + 5


def expected_nonmodal(m: int) -> int:
    return 5 * (m - 1) * (m**2 - m + 1)


def expected_rank_totals(m: int) -> dict[int, int]:
    return {
        0: (m - 1) * (m + 1) * (3 * m + 1),
        1: m * (m - 1) * (3 * m + 5),
        2: (m - 1) * (3 * m**2 + 3 * m - 1),
        3: 2 * m * (m - 1) * (m + 1),
    }


def analyze_modulus(m: int) -> dict:
    payload = exporter.export_layers(m)
    defect_layers = []
    for t, layer in enumerate(payload["layers"]):
        counts: Counter[switches.Row] = Counter(tuple(row) for row in layer)  # type: ignore[arg-type]
        if len(counts) == 1:
            continue
        modal, modal_count = counts.most_common(1)[0]
        words = switches.shortest_words_from(modal)
        rank_totals: Counter[int] = Counter()
        max_word_len = 0
        for row, count in counts.items():
            max_word_len = max(max_word_len, len(words[row]))
            for rank, _ in words[row]:
                rank_totals[rank] += count
        defect_layers.append(
            {
                "layer": t,
                "distinct_rows": len(counts),
                "modal": modal,
                "modal_count": modal_count,
                "nonmodal": m**4 - modal_count,
                "max_word_len": max_word_len,
                "rank_totals": dict(sorted(rank_totals.items())),
            }
        )
    if len(defect_layers) != 1:
        return {"m": m, "ok": False, "reason": "wrong defect layer count", "defect_layers": defect_layers}
    row = defect_layers[0]
    ok = (
        row["layer"] == m - 1
        and row["distinct_rows"] == 26
        and row["modal"] in MODAL_ROW_ROTATIONS
        and row["modal_count"] == expected_modal(m)
        and row["nonmodal"] == expected_nonmodal(m)
        and row["max_word_len"] == 9
        and row["rank_totals"] == expected_rank_totals(m)
    )
    return {
        "m": m,
        "ok": ok,
        "defect": row,
        "expected": {
            "layer": m - 1,
            "distinct_rows": 26,
            "modal_rotations": sorted(MODAL_ROW_ROTATIONS),
            "modal_count": expected_modal(m),
            "nonmodal": expected_nonmodal(m),
            "max_word_len": 9,
            "rank_totals": expected_rank_totals(m),
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--moduli", default="6,8,10,12,14,16,18,20")
    args = parser.parse_args()

    moduli = [int(part) for part in args.moduli.split(",") if part.strip()]
    all_ok = True
    for m in moduli:
        result = analyze_modulus(m)
        all_ok = all_ok and result["ok"]
        defect = result.get("defect")
        print(f"m={m} ok={result['ok']}")
        if defect is not None:
            print(
                "  layer={layer} distinct={distinct_rows} modal_count={modal_count} "
                "nonmodal={nonmodal} max_word_len={max_word_len} rank_totals={rank_totals}".format(
                    **defect
                )
            )
        else:
            print(f"  reason={result.get('reason')}")
    print(f"all_ok={all_ok}")
    if not all_ok:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
