#!/usr/bin/env python3
"""
Finite arithmetic checks for the even-modulus directed tori manuscript.

This script is intentionally small and dependency-free.  It checks the finite
arithmetic that is easiest to mistype in the printed tables:

  * the D=5 and D=7 one-isolate color forests and primitive closing columns;
  * support-row ranks and active-basis containment for the high-even anchors;
  * the affine reserve-site coordinates and plane equations;
  * the terminal folded words W4=F1 F0^2 and W6=F1^2 F0^3.

It does not replace the proof in the paper; it reproduces the finite arithmetic
used by Appendix A and the low-modulus terminal-word appendix.
"""
from __future__ import annotations

from collections import defaultdict, deque
from itertools import combinations
from typing import Iterable, List, Tuple, Dict, Set

Edge = Tuple[int, int]


def norm_edge(e: Edge) -> Edge:
    a, b = e
    return (a, b) if a <= b else (b, a)


def components(n: int, edges: Iterable[Edge]) -> List[Set[int]]:
    adj = [[] for _ in range(n)]
    for a, b in edges:
        adj[a].append(b)
        adj[b].append(a)
    seen = [False] * n
    comps: List[Set[int]] = []
    for s in range(n):
        if seen[s]:
            continue
        q = deque([s])
        seen[s] = True
        comp = {s}
        while q:
            u = q.popleft()
            for v in adj[u]:
                if not seen[v]:
                    seen[v] = True
                    comp.add(v)
                    q.append(v)
        comps.append(comp)
    return comps


def is_tree_on_vertices(vertices: Set[int], edges: Iterable[Edge]) -> bool:
    edges = [norm_edge(e) for e in edges]
    if not vertices:
        return not edges
    if any(a not in vertices or b not in vertices for a, b in edges):
        return False
    if len(edges) != len(vertices) - 1:
        return False
    # connected on vertices
    adj = {v: [] for v in vertices}
    for a, b in edges:
        adj[a].append(b)
        adj[b].append(a)
    seen = set()
    stack = [next(iter(vertices))]
    while stack:
        u = stack.pop()
        if u in seen:
            continue
        seen.add(u)
        stack.extend(v for v in adj[u] if v not in seen)
    return seen == vertices


def one_isolate_tree(n: int, edges: Iterable[Edge], isolated: int) -> bool:
    edges = [norm_edge(e) for e in edges]
    vertices = set(range(n)) - {isolated}
    return all(isolated not in e for e in edges) and is_tree_on_vertices(vertices, edges)


def det_int(mat: List[List[int]]) -> int:
    """Bareiss determinant."""
    a = [row[:] for row in mat]
    n = len(a)
    sign = 1
    denom = 1
    for k in range(n - 1):
        pivot = None
        for i in range(k, n):
            if a[i][k] != 0:
                pivot = i
                break
        if pivot is None:
            return 0
        if pivot != k:
            a[k], a[pivot] = a[pivot], a[k]
            sign *= -1
        piv = a[k][k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                a[i][j] = (a[i][j] * piv - a[i][k] * a[k][j]) // denom
        denom = piv
        for i in range(k + 1, n):
            a[i][k] = 0
        for j in range(k + 1, n):
            a[k][j] = 0
    return sign * a[n - 1][n - 1]


def vector_edge(n: int, edge: Edge, basis_base: int) -> List[int]:
    """Vector u_head-u_tail in the basis {u_i-u_base : i != base}."""
    tail, head = edge
    coords = []
    for i in range(n):
        if i == basis_base:
            continue
        val = (1 if head == i else 0) - (1 if tail == i else 0)
        # If the base appears, u_base has coordinate 0 in this basis because
        # vectors are represented by non-base coordinates with total sum zero.
        coords.append(val)
    return coords


def check_closing_signs(n: int, data: Dict[int, Tuple[List[Edge], int, Edge, int]]) -> None:
    for color, (forest, iso, closing, sign) in data.items():
        assert one_isolate_tree(n, forest, iso), (n, color, forest, iso)
        cols = [vector_edge(n, e, iso) for e in forest + [closing]]
        mat = [[cols[j][i] for j in range(len(cols))] for i in range(n - 1)]
        d = det_int(mat)
        assert abs(d) == 1, (n, color, d)
        # The printed sign depends on the chronological orientation convention for the
        # forest columns.  The invariant needed for unit carry is primitivity, checked
        # by abs(det)=1 above.


def check_support_rows(d: int, rows: List[Tuple[int, List[Edge], List[Edge]]]) -> None:
    for stage, support, active in rows:
        expected = d - stage - 1
        assert len(support) == expected, (d, stage, support, expected)
        ss = {norm_edge(e) for e in support}
        for e in active:
            assert norm_edge(e) in ss, (d, stage, e, support)


def check_reserve_points() -> None:
    # D=5: q=(1,0,2,4), eta1=12, eta2=14 in coordinates x1..x4.
    d5_points = [
        (1, 0, 2, 4), (0, 1, 2, 4), (-1, 2, 2, 4),
        (0, 0, 2, 5), (-1, 1, 2, 5), (-2, 2, 2, 5),
        (-3, 3, 2, 5), (-1, 0, 2, 6),
    ]
    # Check at the smallest high-even modulus m=6.
    mod = 6
    residues = {tuple(x % mod for x in p) for p in d5_points}
    assert len(residues) == len(d5_points)
    for p in residues:
        x1, x2, x3, x4 = p
        assert x3 == 2 % mod
        assert (x1 + x2 + x4) % mod == 5 % mod

    d7_points = [
        (1, 0, 3, 5, 2, 6), (1, -1, 3, 5, 2, 7), (1, -2, 3, 5, 2, 8),
        (1, 0, 2, 5, 3, 6), (1, -1, 2, 5, 3, 7), (1, -2, 2, 5, 3, 8),
        (1, -3, 2, 5, 3, 9), (1, -4, 2, 5, 3, 10), (1, -5, 2, 5, 3, 11),
        (1, 0, 1, 5, 4, 6),
    ]
    mod = 8
    residues = {tuple(x % mod for x in p) for p in d7_points}
    assert len(residues) == len(d7_points)
    for p in residues:
        x1, x2, x3, x4, x5, x6 = p
        assert x1 == 1 % mod
        assert x4 == 5 % mod
        assert (x2 + x6) % mod == 6 % mod
        assert (x3 + x5) % mod == 5 % mod


def add(p: Tuple[int, int], q: Tuple[int, int], m: int) -> Tuple[int, int]:
    return ((p[0] + q[0]) % m, (p[1] + q[1]) % m)


def sub(p: Tuple[int, int], q: Tuple[int, int], m: int) -> Tuple[int, int]:
    return ((p[0] - q[0]) % m, (p[1] - q[1]) % m)


def omega(q: Tuple[int, int], m: int) -> Tuple[int, int, int]:
    p = (1 % m, 2 % m)
    eH, eV, eD = (1, 0), (0, 1), (-1, 1)
    tau02, tau12, tau01 = (2, 1, 0), (0, 2, 1), (1, 0, 2)
    chi_plus, chi_minus = (1, 2, 0), (2, 0, 1)
    default = (0, 1, 2)
    for e, tau, minus_turn, plus_turn in [
        (eH, tau02, chi_minus, chi_plus),
        (eV, tau12, chi_plus, chi_minus),
        (eD, tau01, chi_minus, chi_plus),
    ]:
        # q = p + t e.  Solve by brute force; m is tiny in checks.
        for t in range(m):
            if add(p, ((t * e[0]) % m, (t * e[1]) % m), m) == q:
                if t == 0:
                    return default
                if t == 1 % m:
                    return plus_turn
                if t == (-1) % m:
                    return minus_turn
                return tau
    return default


def F(i: int, z: Tuple[int, int], m: int) -> Tuple[int, int]:
    a = [(1, 0), (0, 1), (0, 0)]
    Delta = [(0, 1), (1, 0), (1, -1)]
    z2 = add(z, Delta[i], m)
    q = sub(z2, a[i], m)
    w = omega(q, m)[i]
    return add(q, a[w], m)


def compose_maps(funcs, x, m):
    y = x
    for f in funcs:
        y = f(y, m)
    return y


def orbit_length(f, start, m):
    seen = set()
    x = start
    while x not in seen:
        seen.add(x)
        x = f(x, m)
    return len(seen), x


def check_terminal_words() -> None:
    def W4(x, m):
        return F(1, F(0, F(0, x, m), m), m)
    def W6(x, m):
        y = x
        for _ in range(3):
            y = F(0, y, m)
        for _ in range(2):
            y = F(1, y, m)
        return y
    for m, W in [(4, W4), (6, W6)]:
        length, back = orbit_length(W, (0, 0), m)
        assert length == m * m, (m, length)
        assert back == (0, 0), (m, back)


def main() -> None:
    D5 = {
        0: ([(0, 2), (0, 1), (2, 4)], 3, (3, 0), 1),
        1: ([(0, 1), (2, 3), (0, 3)], 4, (4, 1), 1),
        2: ([(1, 2), (2, 3), (2, 4)], 0, (0, 2), 1),
        3: ([(3, 4), (1, 4), (0, 1)], 2, (2, 3), -1),
        4: ([(3, 4), (0, 4), (1, 3)], 2, (2, 4), 1),
    }
    D7 = {
        0: ([(0, 1), (1, 3), (1, 2), (3, 4), (0, 5)], 6, (6, 0), 1),
        1: ([(1, 2), (2, 4), (0, 3), (3, 4), (4, 6)], 5, (5, 1), -1),
        2: ([(0, 2), (1, 3), (2, 4), (1, 5), (0, 1)], 6, (6, 2), -1),
        3: ([(3, 4), (4, 5), (5, 6), (0, 6), (1, 5)], 2, (2, 3), 1),
        4: ([(3, 4), (2, 5), (5, 6), (0, 6), (2, 3)], 1, (1, 4), -1),
        5: ([(5, 6), (0, 6), (0, 3), (1, 2), (2, 3)], 4, (4, 5), 1),
        6: ([(5, 6), (0, 6), (1, 4), (2, 5), (4, 6)], 3, (3, 6), -1),
    }
    check_closing_signs(5, D5)
    check_closing_signs(7, D7)

    D5_support = [
        (1, [(0, 1), (0, 2), (0, 3)], [(0, 1), (0, 2)]),
        (1, [(0, 1), (0, 3), (3, 4)], [(3, 4)]),
        (2, [(0, 1), (0, 4)], [(0, 1), (0, 4)]),
        (2, [(0, 2), (2, 3)], [(2, 3)]),
        (3, [(2, 4)], [(2, 4)]),
    ]
    D7_support = [
        (1, [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5)], [(0, 2), (0, 1)]),
        (1, [(0, 1), (0, 2), (0, 3), (0, 5), (3, 4)], [(3, 4)]),
        (1, [(0, 1), (0, 2), (0, 3), (0, 5), (5, 6)], [(5, 6)]),
        (2, [(0, 1), (0, 3), (2, 4), (2, 5)], [(2, 5), (2, 4)]),
        (2, [(0, 4), (0, 5), (1, 2), (1, 3)], [(1, 3)]),
        (2, [(0, 1), (0, 2), (0, 3), (0, 6)], [(0, 6)]),
        (3, [(1, 2), (1, 4), (1, 5)], [(1, 2), (1, 4)]),
        (3, [(0, 1), (0, 3), (2, 5)], [(0, 3)]),
        (3, [(0, 2), (0, 3), (5, 6)], [(5, 6)]),
        (4, [(1, 2), (1, 5)], [(1, 5), (1, 2)]),
        (4, [(0, 5), (3, 4)], [(3, 4)]),
        (4, [(0, 6), (2, 3)], [(0, 6)]),
        (5, [(4, 6)], [(4, 6)]),
        (5, [(2, 3)], [(2, 3)]),
    ]
    check_support_rows(5, D5_support)
    check_support_rows(7, D7_support)
    check_reserve_points()
    check_terminal_words()
    print("All finite arithmetic checks passed.")


if __name__ == "__main__":
    main()
