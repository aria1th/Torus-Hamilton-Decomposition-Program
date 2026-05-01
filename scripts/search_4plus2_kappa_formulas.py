#!/usr/bin/env python3
"""Search simple zero-set kappa formulas for 4+2 bridge certificates."""

from __future__ import annotations

import argparse
import copy
import itertools
import json
from collections import Counter, defaultdict
from pathlib import Path

from verify_4plus2_allN_bridge_cert import (
    BridgeModel,
    PERMS3,
    base_tuple,
    cycle_rank,
    default_bundle_path,
    lambda1_direction,
    load_bundle,
    parse_only,
    validate_certificate,
    verify_certificate,
)


PERM_INDEX = {perm: idx for idx, perm in enumerate(PERMS3)}


def zero_count(xs: tuple[int, int, int, int], m: int) -> int:
    full = (xs[0], xs[1], xs[2], xs[3], (-sum(xs)) % m)
    return sum(1 for value in full if value == 0)


def zero_mask(xs: tuple[int, int, int, int], m: int) -> tuple[bool, bool, bool, bool, bool]:
    full = (xs[0], xs[1], xs[2], xs[3], (-sum(xs)) % m)
    return tuple(value == 0 for value in full)


def full_residues_mod3(xs: tuple[int, int, int, int], m: int) -> tuple[int, int, int, int, int]:
    full = (xs[0], xs[1], xs[2], xs[3], (-sum(xs)) % m)
    return tuple(value % 3 for value in full)


def rotation_perm_index(r: int, reflected: bool) -> int:
    if reflected:
        perm = tuple((r - j) % 3 for j in range(3))
    else:
        perm = tuple((r + j) % 3 for j in range(3))
    return PERM_INDEX[perm]


def affine_value(features: tuple[int, ...], coeffs: tuple[int, ...], modulus: int) -> int:
    return sum(c * x for c, x in zip(coeffs, features)) % modulus


def summarize_feature_dependency(
    m: int, kappa: list[list[int]], feature_name: str, key_fn
) -> dict:
    groups = defaultdict(Counter)
    for t, layer in enumerate(kappa):
        for base, value in enumerate(layer):
            xs = base_tuple(base, m)
            groups[key_fn(t, xs)][value] += 1
    majority = sum(max(counts.values()) for counts in groups.values())
    total = sum(sum(counts.values()) for counts in groups.values())
    impure_examples = []
    for key, counts in groups.items():
        if len(counts) > 1:
            impure_examples.append(
                {
                    "key": repr(key),
                    "counts": dict(sorted(counts.items())),
                }
            )
        if len(impure_examples) >= 5:
            break
    return {
        "feature": feature_name,
        "classes": len(groups),
        "pure_classes": sum(1 for counts in groups.values() if len(counts) == 1),
        "majority_fraction": majority / total if total else 1.0,
        "impure_examples": impure_examples,
    }


def summarize_counter_groups(feature_name: str, groups: dict) -> dict:
    majority = sum(max(counts.values()) for counts in groups.values())
    total = sum(sum(counts.values()) for counts in groups.values())
    impure_examples = []
    for key, counts in groups.items():
        if len(counts) > 1:
            impure_examples.append(
                {
                    "key": repr(key),
                    "counts": {
                        str(value): count for value, count in sorted(counts.items())
                    },
                }
            )
        if len(impure_examples) >= 5:
            break
    return {
        "feature": feature_name,
        "classes": len(groups),
        "pure_classes": sum(1 for counts in groups.values() if len(counts) == 1),
        "majority_fraction": majority / total if total else 1.0,
        "impure_examples": impure_examples,
    }


def kappa_diagnostic_features(m: int, profile: str) -> list[tuple[str, object]]:
    basic_features = [
        ("zero_mask", lambda _t, xs: zero_mask(xs, m)),
        ("zero_count", lambda _t, xs: zero_count(xs, m)),
        ("p", lambda _t, xs: lambda1_direction(xs, 0, m)),
        ("p_zero_count", lambda _t, xs: (lambda1_direction(xs, 0, m), zero_count(xs, m))),
        ("layer_zero_mask", lambda t, xs: (t, zero_mask(xs, m))),
        (
            "layer_p_zero_count",
            lambda t, xs: (t, lambda1_direction(xs, 0, m), zero_count(xs, m)),
        ),
        (
            "layer_mod3_pmod3_zmod3",
            lambda t, xs: (t % 3, lambda1_direction(xs, 0, m) % 3, zero_count(xs, m) % 3),
        ),
        ("layer_mod3_zero_mask", lambda t, xs: (t % 3, zero_mask(xs, m))),
    ]
    residue_features = [
        ("layer_x_mod3", lambda t, xs: (t, tuple(value % 3 for value in xs))),
        ("layer_full_mod3", lambda t, xs: (t, full_residues_mod3(xs, m))),
        (
            "layer_zero_mask_full_mod3",
            lambda t, xs: (t, zero_mask(xs, m), full_residues_mod3(xs, m)),
        ),
        (
            "layer_p_zero_count_full_mod3",
            lambda t, xs: (
                t,
                lambda1_direction(xs, 0, m),
                zero_count(xs, m),
                full_residues_mod3(xs, m),
            ),
        ),
        ("layer_mod3_x_mod3", lambda t, xs: (t % 3, tuple(value % 3 for value in xs))),
        ("layer_mod3_full_mod3", lambda t, xs: (t % 3, full_residues_mod3(xs, m))),
        (
            "layer_mod3_zero_mask_full_mod3",
            lambda t, xs: (t % 3, zero_mask(xs, m), full_residues_mod3(xs, m)),
        ),
    ]
    if profile == "basic":
        return basic_features
    if profile == "residue":
        return residue_features
    if profile == "all":
        return basic_features + residue_features
    raise ValueError(f"unknown diagnostic profile: {profile}")


def kappa_dependency_diagnostics(
    m: int, kappa: list[list[int]], *, profile: str = "basic"
) -> dict:
    flat_values = [value for layer in kappa for value in layer]
    return {
        "profile": profile,
        "perm_counts": dict(sorted(Counter(flat_values).items())),
        "features": [
            summarize_feature_dependency(m, kappa, feature_name, key_fn)
            for feature_name, key_fn in kappa_diagnostic_features(m, profile)
        ],
    }


def section_trace_diagnostics(cert: dict) -> dict:
    validate_certificate(cert)
    m = cert["m"]
    model = BridgeModel(m)
    kappa = cert["kappa_perm_indices"]
    base_period = m**4
    colors = []
    for color, row in enumerate(cert["rows"]):
        base = 0
        forced_events = 0
        kappa_events = 0
        perm_by_layer_p_z = defaultdict(Counter)
        slot_by_layer_p_z_component = defaultdict(Counter)
        slot_by_layer_p_z_component_full_mod3 = defaultdict(Counter)
        for _ in range(base_period):
            for layer, output_slot in enumerate(row):
                event_base = base
                if output_slot < 5:
                    direction = model.base_direction[output_slot][event_base]
                    next_base = model.base_next[output_slot][event_base]
                    if direction == 4:
                        component = 0
                    else:
                        forced_events += 1
                        base = next_base
                        continue
                    base = next_base
                else:
                    component = output_slot - 4

                xs = base_tuple(event_base, m)
                p_value = lambda1_direction(xs, 0, m)
                z_size = zero_count(xs, m)
                residues = full_residues_mod3(xs, m)
                perm_index = kappa[layer][event_base]
                selected_slot = PERMS3[perm_index][component]
                kappa_events += 1
                perm_by_layer_p_z[(layer, p_value, z_size)][perm_index] += 1
                slot_by_layer_p_z_component[
                    (layer, p_value, z_size, component)
                ][selected_slot] += 1
                slot_by_layer_p_z_component_full_mod3[
                    (layer, p_value, z_size, component, residues)
                ][selected_slot] += 1
        if base != 0:
            raise ValueError(f"m={m}: color {color} section trace ended at base {base}")
        total_events = forced_events + kappa_events
        colors.append(
            {
                "color": color,
                "total_events": total_events,
                "forced_events": forced_events,
                "kappa_events": kappa_events,
                "kappa_event_fraction": (
                    kappa_events / total_events if total_events else 0.0
                ),
                "groups": [
                    summarize_counter_groups(
                        "perm_by_layer_p_z", perm_by_layer_p_z
                    ),
                    summarize_counter_groups(
                        "slot_by_layer_p_z_component",
                        slot_by_layer_p_z_component,
                    ),
                    summarize_counter_groups(
                        "slot_by_layer_p_z_component_full_mod3",
                        slot_by_layer_p_z_component_full_mod3,
                    ),
                ],
            }
        )
    return {
        "m": m,
        "base_period": base_period,
        "fiber_period": model.fiber_size,
        "colors": colors,
    }


def build_formula_kappa(
    m: int,
    *,
    a: int,
    b: int,
    c: int,
    d: int,
    reflected: bool,
) -> list[list[int]]:
    table = []
    for t in range(m):
        layer = []
        for base in range(m**4):
            xs = base_tuple(base, m)
            p_value = lambda1_direction(xs, 0, m)
            z_size = zero_count(xs, m)
            r = (a * (t % 3) + b * (p_value % 3) + c * (z_size % 3) + d) % 3
            layer.append(rotation_perm_index(r, reflected))
        table.append(layer)
    return table


def build_dihedral_formula_kappa(
    m: int,
    *,
    rotation: tuple[int, int, int, int],
    reflection: tuple[int, int, int, int],
) -> list[list[int]]:
    table = []
    for t in range(m):
        layer = []
        for base in range(m**4):
            xs = base_tuple(base, m)
            features = (t, lambda1_direction(xs, 0, m), zero_count(xs, m), 1)
            r = affine_value(features, rotation, 3)
            reflected = affine_value(features, reflection, 2) == 1
            layer.append(rotation_perm_index(r, reflected))
        table.append(layer)
    return table


def build_kappa_from_formula(m: int, formula: dict) -> list[list[int]]:
    if formula.get("family") == "dihedral":
        return build_dihedral_formula_kappa(
            m,
            rotation=tuple(formula["rotation"]),
            reflection=tuple(formula["reflection"]),
        )
    return build_formula_kappa(
        m,
        a=formula["a"],
        b=formula["b"],
        c=formula["c"],
        d=formula["d"],
        reflected=formula["reflected"],
    )


def formula_label(a: int, b: int, c: int, d: int, reflected: bool) -> str:
    orientation = "reflected" if reflected else "cyclic"
    return f"{orientation}: r = {a}*t + {b}*p + {c}*z + {d} mod 3"


def dihedral_formula_label(
    rotation: tuple[int, int, int, int], reflection: tuple[int, int, int, int]
) -> str:
    return (
        "dihedral: "
        f"r = {rotation[0]}*t + {rotation[1]}*p + "
        f"{rotation[2]}*z + {rotation[3]} mod 3; "
        f"ref = {reflection[0]}*t + {reflection[1]}*p + "
        f"{reflection[2]}*z + {reflection[3]} mod 2"
    )


def assert_single_cycle_perm(perm: list[int], label: str) -> None:
    size = len(perm)
    seen = bytearray(size)
    state = 0
    for step_count in range(size):
        if not 0 <= state < size:
            raise ValueError(f"{label}: state {state} is outside 0..{size - 1}")
        if seen[state]:
            raise ValueError(f"{label}: repeated state {state} after {step_count} steps")
        seen[state] = 1
        state = perm[state]
    if state != 0:
        raise ValueError(f"{label}: did not return to start 0; ended at {state}")


def format_counter(counter: Counter) -> list[dict]:
    return [
        {"key": key, "count": count}
        for key, count in sorted(counter.items(), key=lambda item: (-item[1], item[0]))
    ]


def compose_section_perm(
    model: BridgeModel,
    row: list[int],
    kappa: list[list[int]],
    base_point: int,
    base_period: int,
) -> list[int]:
    base = base_point
    section_perm = list(range(model.fiber_size))
    for _ in range(base_period):
        for layer, output_slot in enumerate(row):
            if output_slot < 5:
                direction = model.base_direction[output_slot][base]
                next_base = model.base_next[output_slot][base]
                if direction == 4:
                    perm = PERMS3[kappa[layer][base]]
                    fiber_map = model.fiber_next[layer][perm[0]]
                else:
                    fiber_map = model.fiber_forced_q0
                base = next_base
            else:
                perm = PERMS3[kappa[layer][base]]
                fiber_map = model.fiber_next[layer][perm[output_slot - 4]]
            section_perm = [fiber_map[state] for state in section_perm]
    if base != base_point:
        raise ValueError(f"section return left base point {base_point}; ended at base {base}")
    return section_perm


def section_event_plan(
    model: BridgeModel,
    row: list[int],
    base_point: int,
    base_period: int,
) -> tuple[list[int], dict[int, tuple[int, int, int, int]]]:
    base = base_point
    event_keys = []
    key_data = {}
    for _ in range(base_period):
        for layer, output_slot in enumerate(row):
            if output_slot < 5:
                direction = model.base_direction[output_slot][base]
                next_base = model.base_next[output_slot][base]
                if direction == 4:
                    xs = base_tuple(base, model.m)
                    p_value = lambda1_direction(xs, 0, model.m)
                    z_size = zero_count(xs, model.m)
                    key = ((layer * 6 + p_value) * 6 + z_size) * 3
                    event_keys.append(key)
                    key_data[key] = (layer, p_value, z_size, 0)
                else:
                    event_keys.append(-1)
                base = next_base
            else:
                xs = base_tuple(base, model.m)
                component = output_slot - 4
                p_value = lambda1_direction(xs, 0, model.m)
                z_size = zero_count(xs, model.m)
                key = ((layer * 6 + p_value) * 6 + z_size) * 3 + component
                event_keys.append(key)
                key_data[key] = (layer, p_value, z_size, component)
    if base != base_point:
        raise ValueError(f"section return left base point {base_point}; ended at base {base}")
    return event_keys, key_data


def selected_perm_index(formula: dict, layer: int, p_value: int, z_size: int) -> int:
    if formula.get("family") == "dihedral":
        features = (layer, p_value, z_size, 1)
        r = affine_value(features, tuple(formula["rotation"]), 3)
        reflected = affine_value(features, tuple(formula["reflection"]), 2) == 1
        return rotation_perm_index(r, reflected)
    r = (
        formula["a"] * (layer % 3)
        + formula["b"] * (p_value % 3)
        + formula["c"] * (z_size % 3)
        + formula["d"]
    ) % 3
    return rotation_perm_index(r, formula["reflected"])


def fiber_maps_for_formula(
    model: BridgeModel,
    key_data: dict[int, tuple[int, int, int, int]],
    formula: dict,
) -> dict[int, list[int]]:
    maps = {}
    for key, (layer, p_value, z_size, component) in key_data.items():
        perm_index = selected_perm_index(formula, layer, p_value, z_size)
        slot = PERMS3[perm_index][component]
        maps[key] = model.fiber_next[layer][slot]
    return maps


def section_step_from_events(
    model: BridgeModel,
    event_keys: list[int],
    maps: dict[int, list[int]],
    fiber: int,
) -> int:
    for key in event_keys:
        if key < 0:
            fiber = model.fiber_forced_q0[fiber]
        else:
            fiber = maps[key][fiber]
    return fiber


def assert_single_cycle_from_events(
    model: BridgeModel,
    event_keys: list[int],
    maps: dict[int, list[int]],
    label: str,
) -> None:
    report = section_cycle_report(model, event_keys, maps)
    if report["ok"]:
        return
    if report["kind"] == "repeat":
        raise ValueError(
            f"{label}: repeated state {report['state']} after {report['repeat_after']} steps"
        )
    raise ValueError(
        f"{label}: did not return to start 0; ended at {report['end_state']}"
    )


def section_cycle_report(
    model: BridgeModel,
    event_keys: list[int],
    maps: dict[int, list[int]],
) -> dict:
    seen_at = [-1] * model.fiber_size
    state = 0
    for step_count in range(model.fiber_size):
        if seen_at[state] != -1:
            return {
                "ok": False,
                "kind": "repeat",
                "state": state,
                "cycle_start": seen_at[state],
                "cycle_length": step_count - seen_at[state],
                "repeat_after": step_count,
            }
        seen_at[state] = step_count
        state = section_step_from_events(model, event_keys, maps, state)
    if state == 0:
        return {"ok": True, "cycle_length": model.fiber_size}
    return {
        "ok": False,
        "kind": "nonreturn",
        "end_state": state,
        "repeat_after": model.fiber_size,
    }


def section_contexts_for_cert(cert: dict) -> dict:
    validate_certificate(cert)
    m = cert["m"]
    model = BridgeModel(m)
    base_period = m**4
    contexts = []
    for color, row in enumerate(cert["rows"]):
        base_step = lambda base, row=row: model.base_return_step(base, row)
        cycle_rank(
            base_period,
            0,
            base_step,
            f"m={m}: color {color} base return",
        )
        event_keys, key_data = section_event_plan(model, row, 0, base_period)
        contexts.append(
            {
                "color": color,
                "event_keys": event_keys,
                "key_data": key_data,
            }
        )
    return {"m": m, "model": model, "contexts": contexts}


def test_formula_with_section_contexts(section_contexts: dict, formula: dict) -> dict:
    try:
        model = section_contexts["model"]
        for context in section_contexts["contexts"]:
            maps = fiber_maps_for_formula(model, context["key_data"], formula)
            report = section_cycle_report(model, context["event_keys"], maps)
            if not report["ok"]:
                label = (
                    f"m={section_contexts['m']}: color {context['color']} "
                    "fiber section return"
                )
                failure = {"color": context["color"], **report}
                if report["kind"] == "repeat":
                    error = (
                        f"ValueError: {label}: repeated state {report['state']} "
                        f"after {report['repeat_after']} steps"
                    )
                else:
                    error = (
                        f"ValueError: {label}: did not return to start 0; "
                        f"ended at {report['end_state']}"
                    )
                return {"ok": False, "error": error, "failure": failure}
    except Exception as exc:
        return {"ok": False, "error": f"{type(exc).__name__}: {exc}"}
    return {
        "ok": True,
        "message": (
            f"section-verified m={section_contexts['m']} rows=7 "
            "base_cycles=single section_cycles=single"
        ),
    }


def test_formula_section_only(cert: dict, formula: dict) -> dict:
    try:
        section_contexts = section_contexts_for_cert(cert)
    except Exception as exc:
        return {"ok": False, "error": f"{type(exc).__name__}: {exc}"}
    return test_formula_with_section_contexts(section_contexts, formula)


def test_kappa(cert: dict, kappa: list[list[int]], *, section_only: bool) -> dict:
    candidate = copy.deepcopy(cert)
    candidate["kappa_perm_indices"] = kappa
    try:
        if section_only:
            validate_certificate(candidate)
            m = candidate["m"]
            model = BridgeModel(m)
            base_period = m**4
            for color, row in enumerate(candidate["rows"]):
                base_step = lambda base, row=row: model.base_return_step(base, row)
                cycle_rank(
                    base_period,
                    0,
                    base_step,
                    f"m={m}: color {color} base return",
                )
                section_perm = compose_section_perm(
                    model, row, kappa, 0, base_period
                )
                assert_single_cycle_perm(
                    section_perm,
                    f"m={m}: color {color} fiber section return",
                )
            message = (
                f"section-verified m={m} rows=7 "
                "base_cycles=single section_cycles=single"
            )
        else:
            message, _summary = verify_certificate(candidate)
    except Exception as exc:
        return {"ok": False, "error": f"{type(exc).__name__}: {exc}"}
    return {"ok": True, "message": message}


def test_formula(cert: dict, formula: dict, *, section_only: bool) -> dict:
    if section_only:
        return test_formula_section_only(cert, formula)
    return test_kappa(
        cert,
        build_kappa_from_formula(cert["m"], formula),
        section_only=section_only,
    )


def update_failure_summary(summary: dict, result: dict) -> None:
    failure = result.get("failure")
    if failure is None:
        summary["unstructured"] += 1
        return
    color = str(failure.get("color"))
    summary["by_color"][color] += 1
    if failure.get("kind") == "repeat":
        cycle_length = str(failure.get("cycle_length"))
        repeat_after = str(failure.get("repeat_after"))
        summary["by_cycle_length"][cycle_length] += 1
        summary["by_color_cycle_length"][f"{color}:{cycle_length}"] += 1
        summary["by_repeat_after"][repeat_after] += 1
    else:
        summary["nonreturn"] += 1


def empty_failure_summary() -> dict:
    return {
        "by_color": Counter(),
        "by_cycle_length": Counter(),
        "by_color_cycle_length": Counter(),
        "by_repeat_after": Counter(),
        "nonreturn": 0,
        "unstructured": 0,
    }


def finalize_failure_summary(summary: dict) -> dict:
    return {
        "by_color": format_counter(summary["by_color"]),
        "by_cycle_length": format_counter(summary["by_cycle_length"]),
        "by_color_cycle_length": format_counter(summary["by_color_cycle_length"]),
        "by_repeat_after": format_counter(summary["by_repeat_after"]),
        "nonreturn": summary["nonreturn"],
        "unstructured": summary["unstructured"],
    }


def search_formulas(
    cert: dict,
    *,
    stop_after_first: bool,
    include_failures: bool,
    diagnose_hits: bool,
    diagnostic_profile: str,
    section_only: bool,
    max_candidates: int | None,
    summarize_failures: bool,
) -> dict:
    hits = []
    failures = []
    failure_summary = empty_failure_summary() if summarize_failures else None
    candidates_checked = 0
    section_contexts = section_contexts_for_cert(cert) if section_only else None
    for reflected in (False, True):
        for a, b, c, d in itertools.product(range(3), repeat=4):
            if max_candidates is not None and candidates_checked >= max_candidates:
                return {
                    "m": cert["m"],
                    "family": "rotation",
                    "candidates_checked": candidates_checked,
                    "hits": hits,
                    "failures": failures,
                    "truncated": True,
                    **(
                        {"failure_summary": finalize_failure_summary(failure_summary)}
                        if failure_summary is not None
                        else {}
                    ),
                }
            formula = {
                "family": "rotation",
                "a": a,
                "b": b,
                "c": c,
                "d": d,
                "reflected": reflected,
            }
            candidates_checked += 1
            if section_contexts is None:
                result = test_formula(cert, formula, section_only=False)
            else:
                result = test_formula_with_section_contexts(section_contexts, formula)
            record = {
                "formula": formula,
                "label": formula_label(a, b, c, d, reflected),
                "result": result,
            }
            if result["ok"]:
                if diagnose_hits:
                    record["formula_kappa_diagnostics"] = kappa_dependency_diagnostics(
                        cert["m"],
                        build_kappa_from_formula(cert["m"], formula),
                        profile=diagnostic_profile,
                    )
                hits.append(record)
                if stop_after_first:
                    return {
                        "m": cert["m"],
                        "family": "rotation",
                        "candidates_checked": candidates_checked,
                        "hits": hits,
                        "failures": failures,
                    }
            elif include_failures:
                failures.append(record)
            if (not result["ok"]) and failure_summary is not None:
                update_failure_summary(failure_summary, result)
    return {
        "m": cert["m"],
        "family": "rotation",
        "candidates_checked": candidates_checked,
        "hits": hits,
        "failures": failures,
        **(
            {"failure_summary": finalize_failure_summary(failure_summary)}
            if failure_summary is not None
            else {}
        ),
    }


def search_dihedral_formulas(
    cert: dict,
    *,
    stop_after_first: bool,
    include_failures: bool,
    diagnose_hits: bool,
    diagnostic_profile: str,
    section_only: bool,
    max_candidates: int | None,
    summarize_failures: bool,
) -> dict:
    hits = []
    failures = []
    failure_summary = empty_failure_summary() if summarize_failures else None
    candidates_checked = 0
    section_contexts = section_contexts_for_cert(cert) if section_only else None
    for reflection in itertools.product(range(2), repeat=4):
        for rotation in itertools.product(range(3), repeat=4):
            if max_candidates is not None and candidates_checked >= max_candidates:
                return {
                    "m": cert["m"],
                    "family": "dihedral",
                    "candidates_checked": candidates_checked,
                    "hits": hits,
                    "failures": failures,
                    "truncated": True,
                    **(
                        {"failure_summary": finalize_failure_summary(failure_summary)}
                        if failure_summary is not None
                        else {}
                    ),
                }
            formula = {
                "family": "dihedral",
                "rotation": list(rotation),
                "reflection": list(reflection),
            }
            candidates_checked += 1
            if section_contexts is None:
                result = test_formula(cert, formula, section_only=False)
            else:
                result = test_formula_with_section_contexts(section_contexts, formula)
            record = {
                "formula": formula,
                "label": dihedral_formula_label(rotation, reflection),
                "result": result,
            }
            if result["ok"]:
                if diagnose_hits:
                    record["formula_kappa_diagnostics"] = kappa_dependency_diagnostics(
                        cert["m"],
                        build_kappa_from_formula(cert["m"], formula),
                        profile=diagnostic_profile,
                    )
                hits.append(record)
                if stop_after_first:
                    return {
                        "m": cert["m"],
                        "family": "dihedral",
                        "candidates_checked": candidates_checked,
                        "hits": hits,
                        "failures": failures,
                    }
            elif include_failures:
                failures.append(record)
            if (not result["ok"]) and failure_summary is not None:
                update_failure_summary(failure_summary, result)
    return {
        "m": cert["m"],
        "family": "dihedral",
        "candidates_checked": candidates_checked,
        "hits": hits,
        "failures": failures,
        **(
            {"failure_summary": finalize_failure_summary(failure_summary)}
            if failure_summary is not None
            else {}
        ),
    }


def bundled_cases(bundle: Path, only: set[int] | None) -> list[tuple[dict, dict]]:
    return [
        ({"kind": "bundled", "m": cert["m"]}, cert)
        for cert in load_bundle(bundle, only)
    ]


def cover_json_cases(
    path: Path,
    bundle: Path,
    only: set[int] | None,
    max_solutions: int | None,
) -> list[tuple[dict, dict]]:
    payload = json.loads(path.read_text())
    cert_by_m = {cert["m"]: cert for cert in load_bundle(bundle, None)}
    cases = []
    for cover_search in payload.get("cover_searches", []):
        m = cover_search.get("m")
        if only is not None and m not in only:
            continue
        if m not in cert_by_m:
            continue
        for solution_index, solution in enumerate(cover_search.get("solutions", [])):
            if max_solutions is not None and solution_index >= max_solutions:
                break
            cert = copy.deepcopy(cert_by_m[m])
            cert["rows"] = solution["rows"]
            cases.append(
                (
                    {
                        "kind": "cover_json",
                        "path": str(path),
                        "m": m,
                        "solution_index": solution_index,
                        "base_words": solution.get("base_words"),
                    },
                    cert,
                )
            )
    return cases


def hit_cert_filename(source: dict, hit_index: int) -> str:
    kind = source.get("kind", "case")
    m = source.get("m", "unknown")
    solution_index = source.get("solution_index")
    suffix = f"_solution{solution_index}" if solution_index is not None else ""
    return f"bridge_4plus2_m{m}_{kind}{suffix}_formula_hit{hit_index}.json"


def write_hit_certificates(
    output_dir: Path, source: dict, cert: dict, hits: list[dict]
) -> list[str]:
    output_dir.mkdir(parents=True, exist_ok=True)
    paths = []
    for hit_index, hit in enumerate(hits):
        formula = hit["formula"]
        out_cert = copy.deepcopy(cert)
        out_cert["kappa_perm_indices"] = build_kappa_from_formula(cert["m"], formula)
        out_cert["formula_kappa"] = {
            "source": source,
            "formula": formula,
            "label": hit["label"],
        }
        path = output_dir / hit_cert_filename(source, hit_index)
        path.write_text(json.dumps(out_cert, indent=2, sort_keys=True) + "\n")
        paths.append(str(path))
    return paths


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--bundle", type=Path, default=default_bundle_path())
    parser.add_argument("--only", help="comma-separated bundled moduli to test")
    parser.add_argument(
        "--cover-json",
        type=Path,
        help="analyze row solutions from scripts/analyze_4plus2_base_rows.py",
    )
    parser.add_argument(
        "--max-cover-solutions",
        type=int,
        help="maximum number of cover-json solutions to test per modulus",
    )
    parser.add_argument(
        "--emit-hit-cert-dir",
        type=Path,
        help="write verifier-ready certificate JSON files for formula hits",
    )
    parser.add_argument(
        "--all-hits", action="store_true", help="do not stop after first hit"
    )
    parser.add_argument(
        "--formula-family",
        choices=("rotation", "dihedral"),
        default="rotation",
        help="formula family to search",
    )
    parser.add_argument(
        "--section-only",
        action="store_true",
        help="during formula search, check base and fiber section cycles but skip product-cycle audit",
    )
    parser.add_argument(
        "--max-candidates",
        type=int,
        help="stop each formula search after this many candidates",
    )
    parser.add_argument(
        "--summarize-failures",
        action="store_true",
        help="summarize first section-return failures across formula candidates",
    )
    parser.add_argument("--include-failures", action="store_true")
    parser.add_argument(
        "--diagnose-kappa",
        action="store_true",
        help="add dependency diagnostics for input kappa tables and formula hits",
    )
    parser.add_argument(
        "--diagnostics-only",
        action="store_true",
        help="only emit input kappa diagnostics; skip formula verification",
    )
    parser.add_argument(
        "--diagnostic-profile",
        choices=("basic", "residue", "all"),
        default="basic",
        help="feature set for --diagnose-kappa or --diagnostics-only",
    )
    parser.add_argument(
        "--section-trace-diagnostics",
        action="store_true",
        help="summarize bundled/generated kappa behavior along each section-return trace",
    )
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()
    only = parse_only(args.only)
    if args.cover_json is None:
        cases = bundled_cases(args.bundle, only)
    else:
        cases = cover_json_cases(
            args.cover_json, args.bundle, only, args.max_cover_solutions
        )

    payload = {
        "description": (
            "Search simple zero-set kappa formula families for the 4+2 bridge."
        ),
        "searches": [],
    }
    for source, cert in cases:
        if args.diagnostics_only:
            result = {"m": cert["m"], "hits": [], "failures": []}
        elif args.formula_family == "dihedral":
            result = search_dihedral_formulas(
                cert,
                stop_after_first=not args.all_hits,
                include_failures=args.include_failures,
                diagnose_hits=args.diagnose_kappa,
                diagnostic_profile=args.diagnostic_profile,
                section_only=args.section_only,
                max_candidates=args.max_candidates,
                summarize_failures=args.summarize_failures,
            )
        else:
            result = search_formulas(
                cert,
                stop_after_first=not args.all_hits,
                include_failures=args.include_failures,
                diagnose_hits=args.diagnose_kappa,
                diagnostic_profile=args.diagnostic_profile,
                section_only=args.section_only,
                max_candidates=args.max_candidates,
                summarize_failures=args.summarize_failures,
            )
        result["source"] = source
        if args.diagnose_kappa or args.diagnostics_only:
            result["input_kappa_diagnostics"] = kappa_dependency_diagnostics(
                cert["m"],
                cert["kappa_perm_indices"],
                profile=args.diagnostic_profile,
            )
        if args.section_trace_diagnostics:
            result["section_trace_diagnostics"] = section_trace_diagnostics(cert)
        if args.emit_hit_cert_dir is not None and result["hits"]:
            result["emitted_cert_json"] = write_hit_certificates(
                args.emit_hit_cert_dir, source, cert, result["hits"]
            )
        payload["searches"].append(result)
    text = json.dumps(payload, indent=2, sort_keys=True)
    if args.json_out is None:
        print(text)
    else:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(text + "\n")
        print(f"wrote {args.json_out}")


if __name__ == "__main__":
    main()
