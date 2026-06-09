#!/usr/bin/env python3
"""
Computed audit for the D5(4) H2 realization slot.

This script checks the finite consequences of the paper definitions against the
current Lean candidates.  It is intentionally not a certificate generator.  It
answers a narrower engineering question:

  * which local interpretations reproduce the paper's abstract return maps?
  * which existing finite/root-flat schedules are valid but not the paper H2
    realization handoff currently required by `LowD5M4RibbonInterface`?

The checks mirror:

  * `TerminalA2LowMod.terminalOmega` and `terminalReturn`,
  * `LowD5M4Seed.fullReturn`,
  * the standard D5(4) root-flat `rootStep`,
  * active finite witnesses under `EvenV11/`, with archive fallback.
"""

from __future__ import annotations

import re
from collections import Counter, defaultdict
from itertools import product
from math import lcm
from pathlib import Path
from typing import Callable, Iterable

M = 4
ROOT_STATES = list(product(range(M), repeat=4))
Q_STATES = list(product(range(M), repeat=2))
LAYERS = range(M)
COLORS5 = range(5)
COLORS3 = range(3)

REPO = Path(__file__).resolve().parents[1]


Q = tuple[int, int]
Root4 = tuple[int, int, int, int]


def addq(a: Q, b: Q) -> Q:
    return ((a[0] + b[0]) % M, (a[1] + b[1]) % M)


def subq(a: Q, b: Q) -> Q:
    return ((a[0] - b[0]) % M, (a[1] - b[1]) % M)


TERMINAL_P = (1, 2)
EH = (1, 0)
EV = (0, 1)
ED = (-1, 1)
VERTEX = [(1, 0), (0, 1), (0, 0)]
DELTA = [(0, 1), (1, 0), (1, -1)]


def omega(q: Q) -> tuple[int, int, int]:
    """The paper terminal word omega_4, matching TerminalA2LowMod.terminalOmega."""
    default = (0, 1, 2)
    tau02 = (2, 1, 0)
    tau12 = (0, 2, 1)
    tau01 = (1, 0, 2)
    chi_plus = (1, 2, 0)
    chi_minus = (2, 0, 1)

    if q == TERMINAL_P:
        return default
    if q == subq(TERMINAL_P, EH):
        return chi_minus
    if q == addq(TERMINAL_P, EH):
        return chi_plus
    if q == subq(TERMINAL_P, EV):
        return chi_plus
    if q == addq(TERMINAL_P, EV):
        return chi_minus
    if q == subq(TERMINAL_P, ED):
        return chi_minus
    if q == addq(TERMINAL_P, ED):
        return chi_plus
    if q[1] == 2:
        return tau02
    if q[0] == 1:
        return tau12
    if (q[0] + q[1]) % M == 3:
        return tau01
    return default


def terminal_return(i: int, q: Q) -> Q:
    """The paper run-collapsed terminal return F_i."""
    z = addq(q, DELTA[i])
    tail = subq(z, VERTEX[i])
    return addq(tail, VERTEX[omega(tail)[i]])


RESET_SITES = [(0, 0), (1, 0), (2, 2)]
LIFT_SITES = [
    ((0, 0), 0),
    ((0, 0), 1),
    ((0, 0), 2),
    ((0, 0), 3),
    ((0, 1), 0),
]


def base_return(c: int, qy: tuple[Q, int]) -> tuple[Q, int]:
    """LowD5M4Seed.baseReturn."""
    q, y = qy
    if c < 3:
        return terminal_return(c, q), (y + int(q == RESET_SITES[c])) % M
    if c == 3:
        return (terminal_return(0, q) if y == 0 else q), (y + 1) % M
    if c == 4:
        if y == 1:
            q = terminal_return(0, q)
        elif y == 2:
            q = terminal_return(2, q)
        elif y == 3:
            q = terminal_return(1, q)
        return q, (y + 1) % M
    raise ValueError(c)


def full_return(c: int, x: Root4) -> Root4:
    """LowD5M4Seed.fullReturn, represented as (q0,q1,y,z)."""
    q = (x[0], x[1])
    y = x[2]
    z = x[3]
    q2, y2 = base_return(c, (q, y))
    if (q, y) == LIFT_SITES[c]:
        z = (z + 1) % M
    return (q2[0], q2[1], y2, z)


def root_step_d5(direction: int, w: Root4) -> Root4:
    """LowD5M4Schedule.rootStep in tuple coordinates."""
    if direction == 4:
        return w
    out = list(w)
    out[direction] = (out[direction] + 1) % M
    return tuple(out)  # type: ignore[return-value]


def root_step_d3(direction: int, q: Q) -> Q:
    """Standard D3 root step on two root coordinates."""
    if direction == 2:
        return q
    out = list(q)
    out[direction] = (out[direction] + 1) % M
    return tuple(out)  # type: ignore[return-value]


STD_DIR5 = {0: 0, 1: 1, 2: 4}
LIFT_Y = 2
LIFT_Z = 3


def q_of(w: Root4) -> Q:
    return (w[0], w[1])


def terminal_std_row_at_q(q: Q) -> list[int]:
    """The naive `terminalStdBaseRowEquiv5 q` row."""
    row = omega(q)
    return [STD_DIR5[row[0]], STD_DIR5[row[1]], STD_DIR5[row[2]], LIFT_Y, LIFT_Z]


def swap_outputs(row: Iterable[int], color: int, direction: int) -> list[int]:
    """Post-compose a row by swapping `row[color]` and `direction`."""
    out = list(row)
    source_dir = out[color]
    for i, value in enumerate(out):
        if value == source_dir:
            out[i] = direction
        elif value == direction:
            out[i] = source_dir
    return out


def first_lift(row: Iterable[int], w: Root4) -> list[int]:
    out = list(row)
    q = q_of(w)
    for i, site in enumerate(RESET_SITES):
        if q == site:
            out = swap_outputs(out, i, LIFT_Y)
    return out


def final_lift(row: Iterable[int], w: Root4) -> list[int]:
    out = list(row)
    q = q_of(w)
    y = w[2]
    for c, site in enumerate(LIFT_SITES):
        if (q, y) == site:
            out = swap_outputs(out, c, LIFT_Z)
    return out


RowFn = Callable[[int, Root4], list[int]]


def d5_return_map(row_fn: RowFn, c: int, w: Root4) -> Root4:
    for t in LAYERS:
        w = root_step_d5(row_fn(t, w)[c], w)
    return w


def verify_d5_rows(row_fn: RowFn) -> tuple[bool, bool, list[tuple[int, Root4]], object]:
    rf1 = all(sorted(row_fn(t, w)) == [0, 1, 2, 3, 4] for t in LAYERS for w in ROOT_STATES)

    rf2 = True
    first_rf2_fail: object = None
    for t in LAYERS:
        for c in COLORS5:
            image = [root_step_d5(row_fn(t, w)[c], w) for w in ROOT_STATES]
            if len(set(image)) != len(ROOT_STATES):
                counts = Counter(image)
                duplicate = next((x, k) for x, k in counts.items() if k > 1)
                missing = next(w for w in ROOT_STATES if w not in counts)
                first_rf2_fail = (t, c, len(set(image)), duplicate, missing)
                rf2 = False
                break
        if not rf2:
            break

    cycles: list[tuple[int, Root4]] = []
    for c in COLORS5:
        seen = set()
        x = ROOT_STATES[0]
        while x not in seen:
            seen.add(x)
            x = d5_return_map(row_fn, c, x)
        cycles.append((len(seen), x))
    return rf1, rf2, cycles, first_rf2_fail


def common_conjugacy_count(
    domain: list[object],
    codomain: list[object],
    target: list[Callable[[object], object]],
    actual: list[Callable[[object], object]],
    start: object,
) -> int:
    """Count common bijections e with actual_c(e(x)) = e(target_c(x))."""
    count = 0
    for image_start in codomain:
        e = {start: image_start}
        inv = {image_start: start}
        stack = [start]
        ok = True
        while stack and ok:
            x = stack.pop()
            wx = e[x]
            for target_c, actual_c in zip(target, actual):
                y = target_c(x)
                wy = actual_c(wx)
                if y in e:
                    if e[y] != wy:
                        ok = False
                        break
                elif wy in inv:
                    ok = False
                    break
                else:
                    e[y] = wy
                    inv[wy] = y
                    stack.append(y)
        if ok and len(e) == len(domain):
            count += 1
    return count


def check_abstract_full_return() -> None:
    for c in COLORS5:
        seen = set()
        x = ROOT_STATES[0]
        while x not in seen:
            seen.add(x)
            x = full_return(c, x)
        assert len(seen) == 256 and x == ROOT_STATES[0], (c, len(seen), x)
    print("[ok] LowD5M4Seed.fullReturn R_hat_0..R_hat_4 are 256-cycles")


def check_naive_and_split_rows() -> None:
    def naive(t: int, w: Root4) -> list[int]:
        return terminal_std_row_at_q(q_of(w))

    rf1, rf2, cycles, fail = verify_d5_rows(naive)
    assert rf1 and rf2 and fail is None
    assert cycles != [(256, ROOT_STATES[0])] * 5

    actual = [lambda w, c=c: d5_return_map(naive, c, w) for c in COLORS5]
    target = [lambda x, c=c: full_return(c, x) for c in COLORS5]
    conj = common_conjugacy_count(ROOT_STATES, ROOT_STATES, target, actual, ROOT_STATES[0])
    assert conj == 0
    print("[ok] naive terminalStdBaseRowAtState rows: RF1/RF2 hold, RF3/paper conjugacy fail")

    split_rf2_hits = []
    for ty in LAYERS:
        for tz in LAYERS:
            def split(t: int, w: Root4, ty: int = ty, tz: int = tz) -> list[int]:
                row = terminal_std_row_at_q(q_of(w))
                if t == ty:
                    row = first_lift(row, w)
                if t == tz:
                    row = final_lift(row, w)
                return row

            split_rf1, split_rf2, _cycles, _fail = verify_d5_rows(split)
            assert split_rf1
            if split_rf2:
                split_rf2_hits.append((ty, tz))

    assert split_rf2_hits == []
    print("[ok] naive rows plus separated Y/Z substitutions: all 16 layer splits fail RF2")


def check_color_anchored_terminal_dir() -> None:
    def direction(q: Q, c: int) -> int:
        # The currently sketched D3TerminalA2Parametric terminalDir shape:
        # terminalRowEquiv (omega (q - a_c)) c.
        return omega(subq(q, VERTEX[c]))[c]

    bad = next(q for q in Q_STATES if sorted(direction(q, c) for c in COLORS3) != [0, 1, 2])
    row = [direction(bad, c) for c in COLORS3]
    assert bad == (0, 0) and row == [1, 2, 2]
    print("[ok] color-anchored terminalDir is not RF1 at q=(0,0): row [1,2,2]")


def compose_perm(p: tuple[int, ...], q: tuple[int, ...]) -> tuple[int, ...]:
    """Permutation composition `p ∘ q`, represented by image tuples."""
    return tuple(p[q[i]] for i in range(len(q)))


def invert_perm(p: tuple[int, ...]) -> tuple[int, ...]:
    out = [0] * len(p)
    for i, j in enumerate(p):
        out[j] = i
    return tuple(out)


def perm_order(p: tuple[int, ...]) -> int:
    seen = [False] * len(p)
    out = 1
    for i in range(len(p)):
        if seen[i]:
            continue
        j = i
        length = 0
        while not seen[j]:
            seen[j] = True
            length += 1
            j = p[j]
        out = lcm(out, length)
    return out


def check_terminal_relation_invariants() -> None:
    q_index = {q: i for i, q in enumerate(Q_STATES)}
    f0 = tuple(q_index[terminal_return(0, q)] for q in Q_STATES)
    f2 = tuple(q_index[terminal_return(2, q)] for q in Q_STATES)
    assert perm_order(compose_perm(f0, f2)) == 33
    print("[ok] terminal relation invariant: order(F0 o F2) = 33")


def enumerate_terminal_layer_maps() -> list[tuple[tuple[int, ...], tuple[int, ...]]]:
    """All bijective standard D3 root-flat layer maps `q ↦ q + a_{d(q)}`."""
    q_index = {q: i for i, q in enumerate(Q_STATES)}
    layer_edges = [
        [q_index[root_step_d3(d, q)] for d in COLORS3]
        for q in Q_STATES
    ]
    maps: list[tuple[tuple[int, ...], tuple[int, ...]]] = []
    dirs: list[int | None] = [None] * len(Q_STATES)

    def go(used: int) -> None:
        if all(d is not None for d in dirs):
            dir_tuple = tuple(d for d in dirs if d is not None)
            perm = tuple(layer_edges[i][dir_tuple[i]] for i in range(len(Q_STATES)))
            maps.append((perm, dir_tuple))
            return

        best = -1
        best_choices: list[int] | None = None
        for i, direction in enumerate(dirs):
            if direction is not None:
                continue
            choices = [
                d for d, target in enumerate(layer_edges[i])
                if not ((used >> target) & 1)
            ]
            if best_choices is None or len(choices) < len(best_choices):
                best = i
                best_choices = choices
                if len(choices) <= 1:
                    break
        assert best_choices is not None
        for d in best_choices:
            target = layer_edges[best][d]
            dirs[best] = d
            go(used | (1 << target))
            dirs[best] = None

    go(0)
    return maps


def check_standard_terminal_chart_not_four_layer_realization() -> None:
    """The fixed chart `TerminalRootState ≃ Q4` is too rigid.

    Even before coupling colors by RF1, no single `F_i` factors as four
    standard D3 root-flat layer bijections.  The terminal realization theorem
    therefore needs a genuine return-section equivalence, not the plain chart.
    """
    layer_maps = enumerate_terminal_layer_maps()
    assert len(layer_maps) == 417

    pair_products: dict[tuple[int, ...], int] = defaultdict(int)
    for left, _left_dirs in layer_maps:
        for right, _right_dirs in layer_maps:
            pair_products[compose_perm(right, left)] += 1

    q_index = {q: i for i, q in enumerate(Q_STATES)}
    for c in COLORS3:
        target = tuple(q_index[terminal_return(c, q)] for q in Q_STATES)
        has_factorization = False
        for first_pair in pair_products:
            needed_second_pair = compose_perm(target, invert_perm(first_pair))
            if needed_second_pair in pair_products:
                has_factorization = True
                break
        assert not has_factorization, c

    print(
        "[ok] standard terminalRootEquiv target: no F_i has a 4-layer "
        "standard-root bijective factorization"
    )


def parse_d3_even_m4_dir_words() -> dict[tuple[int, int, int], tuple[int, int, int]]:
    text = (REPO / "EvenV11/D3EvenM4.lean").read_text()
    body = text.split("def dirWordNat", 1)[1].split("def colorDir", 1)[0]
    entries: dict[tuple[int, int, int], tuple[int, int, int]] = {}
    pattern = re.compile(
        r"\|\s*(\d+),\s*(\d+),\s*(\d+)\s*=>\s*\((\d+),\s*(\d+),\s*(\d+)\)"
    )
    for match in pattern.finditer(body):
        a, b, c, d0, d1, d2 = map(int, match.groups())
        entries[(a, b, c)] = (d0 % 3, d1 % 3, d2 % 3)
    assert len(entries) == 64
    return entries


def check_d3_even_m4_not_terminal_f() -> None:
    d3_file = REPO / "EvenV11/D3EvenM4.lean"
    if not d3_file.exists():
        print("[skip] D3EvenM4.lean is absent in this H2-focused bundle")
        return
    entries = parse_d3_even_m4_dir_words()

    def layer_vertex(t: int, q: Q) -> tuple[int, int, int]:
        return (q[0], q[1], (t - q[0] - q[1]) % M)

    def layer_map(t: int, c: int, q: Q) -> Q:
        return root_step_d3(entries[layer_vertex(t, q)][c], q)

    def ret(c: int, q: Q) -> Q:
        for t in LAYERS:
            q = layer_map(t, c, q)
        return q

    assert all(sorted(entries[v]) == [0, 1, 2] for v in product(range(M), repeat=3))
    for t in LAYERS:
        for c in COLORS3:
            assert len({layer_map(t, c, q) for q in Q_STATES}) == 16

    for c in COLORS3:
        seen = set()
        q = Q_STATES[0]
        while q not in seen:
            seen.add(q)
            q = ret(c, q)
        assert len(seen) == 16 and q == Q_STATES[0]

    target = [lambda q, c=c: terminal_return(c, q) for c in COLORS3]
    actual = [lambda q, c=c: ret(c, q) for c in COLORS3]
    q_index = {q: i for i, q in enumerate(Q_STATES)}
    target_perm = [
        tuple(q_index[terminal_return(c, q)] for q in Q_STATES)
        for c in COLORS3
    ]
    actual_perm = [
        tuple(q_index[ret(c, q)] for q in Q_STATES)
        for c in COLORS3
    ]
    target_f0f2_order = perm_order(compose_perm(target_perm[0], target_perm[2]))
    actual_f0f2_order = perm_order(compose_perm(actual_perm[0], actual_perm[2]))
    assert target_f0f2_order == 33
    assert actual_f0f2_order == 63

    conj = common_conjugacy_count(Q_STATES, Q_STATES, target, actual, Q_STATES[0])
    assert conj == 0
    print(
        "[ok] D3EvenM4 finite base is RF-valid but has no common conjugacy "
        "to terminal F_i; order(R0 o R2) = 63, not 33"
    )


def parse_nat_array(path: Path, name: str) -> list[int]:
    text = path.read_text()
    match = re.search(rf"def {name} : Array Nat :=\s*#\[(.*?)\n\]", text, re.S)
    assert match, name
    return [int(x) for x in re.findall(r"\d+", match.group(1))]


def check_lowd5m4_finite_not_paper_conj() -> None:
    active = REPO / "EvenV11/LowD5M4Finite.lean"
    archive = REPO / "archive/EvenV11/LowD5M4Finite.lean"
    path = active if active.exists() else archive
    if not path.exists():
        print("[skip] LowD5M4Finite.lean is absent")
        return

    dir_table = parse_nat_array(path, "dirTable")
    step_table = parse_nat_array(path, "stepTable")
    assert len(dir_table) == 4 * 256 * 5
    assert len(step_table) == 5 * 256

    def direction(t: int, w: int, c: int) -> int:
        return dir_table[(t * 256 + w) * 5 + c]

    def step(direction: int, w: int) -> int:
        return step_table[direction * 256 + w]

    def layer_map(t: int, c: int, w: int) -> int:
        return step(direction(t, w, c), w)

    def ret(c: int, w: int) -> int:
        for t in LAYERS:
            w = layer_map(t, c, w)
        return w

    finite_states = list(range(256))
    assert all(sorted(direction(t, w, c) for c in COLORS5) == [0, 1, 2, 3, 4]
               for t in LAYERS for w in finite_states)
    for t in LAYERS:
        for c in COLORS5:
            assert len({layer_map(t, c, w) for w in finite_states}) == 256
    for c in COLORS5:
        seen = set()
        w = 0
        while w not in seen:
            seen.add(w)
            w = ret(c, w)
        assert len(seen) == 256 and w == 0

    target = [lambda x, c=c: full_return(c, x) for c in COLORS5]
    actual = [lambda w, c=c: ret(c, w) for c in COLORS5]
    conj = common_conjugacy_count(ROOT_STATES, finite_states, target, actual, ROOT_STATES[0])
    assert conj == 0
    location = "active" if path == active else "archive"
    print(
        f"[ok] {location} LowD5M4Finite is RF-valid and closes direct H2, "
        "but has no common conjugacy to paper fullReturn"
    )


def main() -> None:
    check_abstract_full_return()
    check_naive_and_split_rows()
    check_color_anchored_terminal_dir()
    check_terminal_relation_invariants()
    check_standard_terminal_chart_not_four_layer_realization()
    check_d3_even_m4_not_terminal_f()
    check_lowd5m4_finite_not_paper_conj()
    print("[ok] conclusion: direct H2 is closed; paper-faithful H2 still needs a genuine terminal/ribbon realization theorem")


if __name__ == "__main__":
    main()
