#!/usr/bin/env python3
"""Finite transcription checks for even_directed_tori.tex.

Uses no retained constructors, optimization packages, or proof-search output.
This is supplementary finite testing, not a formal or all-parameter proof.
Run: python check_manuscript.py --out MANUSCRIPT_CHECK_REPORT.json
"""
from __future__ import annotations
import argparse
from collections import defaultdict
from itertools import product
import json
from math import gcd
from pathlib import Path

class VerificationError(RuntimeError):
    pass

def require(condition: bool, message: str) -> None:
    if not condition:
        raise VerificationError(message)

def cycles(p):
    n = len(p)
    require(sorted(p) == list(range(n)), 'not a permutation')
    seen = bytearray(n)
    out = []
    for x in range(n):
        if seen[x]:
            continue
        C = []
        y = x
        while not seen[y]:
            seen[y] = 1
            C.append(y)
            y = p[y]
        require(y == x, 'orbit does not close at its initial vertex')
        out.append(C)
    return out

def near_row(m, v):
    x, y, w = v
    h = (x+y+w) % m
    if h == 0:
        return (2, 1, 0)
    if h == 1:
        return (0, 2, 1) if w in (0, 1) else (1, 2, 0)
    if h == 2 and w == 0:
        return (1, 0, 2)
    return (0, 1, 2)

def defect_label(m, v):
    return (v[2] - max(sum(v) % m - 2, 0)) % 2

def star_row(m, a, b):
    a %= m
    b %= m
    if (a, b) == (0, 0):
        return (0, 1, 2)
    if (a+b) % m == 0:
        z, t = 0, a
    elif a == 0:
        z, t = 1, b
    elif b == 0:
        z, t = 2, (-a) % m
    else:
        return (0, 1, 2)
    if t == 1:
        return (2, 0, 1)
    if t == m-1:
        return (1, 2, 0)
    return tuple((2*z-c) % 3 for c in range(3))

def terminal_row(m, v):
    x, y, w = v
    h = (x+y+w) % m
    if h == 1:
        row = star_row(m, y, w-3)
    else:
        s = 1 if h == 2 else 2 if (m % 3 != 0 or h in (0, 3, 4)) else 0
        row = tuple((c+s) % 3 for c in range(3))
    return tuple(row[c] for c in (0, 2, 1))

def shell_row(m, p, h, w):
    k = p//2
    # A_i = i; B_i = p+i.
    if h == 0:
        W = {p} | set(range(1, p))
        pairs = [(0, p+1)]
    elif h == 1:
        W = {0} | set(range(p+1, 2*p))
        if p % 2 == 0:
            pairs = [(p, 1)] + [(i, i+1) for i in range(2, p, 2)]
        else:
            pairs = [(i, i+1) for i in range(1, p, 2)]
    else:
        W = set(range(p))
        if h != 2:
            pairs = []
        elif p % 2 == 0:
            pairs = [(p+i, p+i+1) for i in range(2, p, 2)]
        else:
            pairs = [(p, p+2)] + [(p+i, p+i+1) for i in range(3, p, 2)]
    V = set(range(2*p)) - W
    used = {v for e in pairs for v in e}
    require(used <= V and len(used) == 2*len(pairs), 'shell pair inconsistency')
    fillers = sorted(V-used)[:k-len(pairs)]
    require(0 <= k-len(pairs) == len(fillers), 'shell filler count')
    Y = set(fillers)
    for j, (a, b) in enumerate(pairs):
        Y.add(b if w == (1 if j == 1 else 0) else a)
    require(len(Y) == k and Y <= V, 'shell row quota')
    return tuple(2 if c in W else 1 if c in Y else 0 for c in range(2*p))

def physical_factors(m, row_fn, widths):
    n = m**3
    d = sum(widths)
    result = [[0]*n for _ in range(d)]
    all_vertices = list(product(range(m), repeat=3))
    for index, v in enumerate(all_vertices):
        ds = tuple(row_fn(v))
        require(len(ds) == d and all(ds.count(i) == widths[i] for i in range(3)),
                'physical direction quota')
        for c, direction in enumerate(ds):
            head = list(v)
            head[direction] = (head[direction]+1) % m
            result[c][index] = (head[0]*m+head[1])*m+head[2]
    C = [cycles(P) for P in result]
    return result, C, all_vertices

def components(supports, labels):
    par = {c: c for c in labels}
    def root(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x
    for S in supports:
        S = list(S)
        if S:
            for c in S[1:]:
                par[root(c)] = root(S[0])
    G = defaultdict(set)
    for c in labels:
        G[root(c)].add(c)
    return {frozenset(S) for S in G.values()}

def explicit_cycle(order):
    return {x: order[(i+1) % len(order)] for i, x in enumerate(order)}

def appendix_check(m):
    lam = -2 if m % 3 else 3
    Cplus, Cminus = (1, m-1), (m-1, 1)
    Q = [Cplus] + [(s, 0) for s in range(1,m)] + [Cminus] + [(0,s) for s in range(1,m)]
    qset = set(Q)
    require(len(qset) == 2*m, 'star support repeats')
    P = explicit_cycle(Q)
    # Direct special-layer map, rather than assuming the displayed P cycle.
    g = [(0,0), (1,0), (0,1)]
    for a,b in product(range(m),repeat=2):
        dr = star_row(m,a,b)[0]
        actual = ((a+g[dr][0])%m, (b+g[dr][1])%m)
        require(actual == P.get((a,b),(a,b)), f'P0 cycle formula at m={m}')
    nu = {}
    translation_roof = {}
    for a,b in Q:
        v = (a,b)
        for t in range(1,m+1):
            v = ((v[0]+1)%m, (v[1]+lam)%m)
            if v in qset:
                nu[a,b] = v
                translation_roof[a,b] = t
                break
        else:
            raise VerificationError('translation misses return support')
    require(sum(translation_roof.values()) == m*m, 'Q does not cover all translation orbits')
    Phi = {v: nu[P[v]] for v in Q}
    psi, roof = {}, {}
    for s in range(1,m):
        v = (s,0)
        for t in range(1,2*m+1):
            v = Phi[v]
            if v[1] == 0 and v[0] != 0:
                psi[s], roof[s] = v[0], t
                break
        else:
            raise VerificationError('missing X first return')
    expected, expected_roof = {}, {}
    if m % 3:
        k = m//2
        for s in range(1,m):
            if s <= k-2:
                expected[s], expected_roof[s] = s+k+1,1
            elif s == k-1:
                expected[s], expected_roof[s] = k,1
            elif s <= 2*k-3:
                expected[s], expected_roof[s] = s-k+2,3
            elif s == 2*k-2:
                expected[s], expected_roof[s] = k+1,4
            else:
                expected[s], expected_roof[s] = 1,3
        theta = explicit_cycle([1,k,k+1])
        for s in range(1,m):
            b = (s+k+1-1)%(m-1)+1
            require(expected[s] == theta.get(b,b), 'nondivisible theta formula')
    elif m == 6:
        expected = explicit_cycle([1,4,3,2,5])
        expected_roof = dict(zip(range(1,6), [1,1,1,5,4]))
    else:
        q = m//6
        a = 2*q+1
        theta = {s:s for s in range(1,m)}
        theta.update({1:a-1,2:1,3:a,a-1:a-2,a:a-3})
        theta.update({s:s-2 for s in range(4,a-1)})
        for s in range(1,m):
            expected[s] = theta[(s+a-1)%(m-1)+1]
            expected_roof[s] = (1 if s <= 4*q-1 else 5 if s in (4*q,6*q-2)
                                else 4 if s <= 6*q-3 else 3)
        order = list(range(1,a-3,2))+[a-3,a-1,a]+list(range(2,a-4,2))+[a-2]
        require(sorted(order) == list(range(1,a+1)), 'small star cycle labels')
        small = explicit_cycle(order)
        require(all(small[s] == theta[(s+4-1)%a+1] for s in order), 'small star cycle transitions')
    require(psi == expected and roof == expected_roof, f'appendix return table m={m}')
    require(sum(roof.values()) == 2*m, 'missing Phi orbits')
    cyc = cycles([psi[s]-1 for s in range(1,m)])
    require(len(cyc) == 1, 'star return is not one cycle')
    return len(Q),sum(translation_roof.values())

def incidence_check(m,p):
    supports = [[],[],[]]
    xsupports = []
    hws = list(product(range(m),repeat=2))
    for h,w in hws:
        v = (0,(h-w)%m,w)
        lab = defect_label(m,v)
        ds = near_row(m,v)+shell_row(m,p,h,w)
        for direction in range(3):
            S = []
            for color,dr in enumerate(ds):
                if dr != direction:
                    continue
                S.append(color if color < 2 else 2+lab if color == 2 else color+1)
            supports[direction].append(S)
        xsupports.append({c for c,dr in enumerate(shell_row(m,p,h,w)) if dr==0})
    for S in supports:
        require(components(S,range(2*p+4)) == {frozenset(range(2*p+4))}, 'seed incidence disconnected')
    ah = [(1,0),(2,0),(0,0),(1,3)]
    mates = [p,p+1,0,1 if p%2==0 else 2]
    for hw,mat in zip(ah,mates):
        S = xsupports[hws.index(hw)]
        require(mat in S, 'ineligible entry mate')
        S.remove(mat)
    got = components(xsupports,range(2*p))
    want = ({frozenset([0]),frozenset([p]),frozenset(range(1,p)),frozenset(range(p+1,2*p))}
            if p%2==0 else {frozenset([0]),frozenset(range(1,2*p))})
    require(got == want, f'residual component formula m={m},p={p}')
    require(all(len(set(G)-set(mates))%2==0 for G in got), 'unmatched component parity')

def length_counterexample():
    m,n = 4,6
    S = [(x+1)%n for x in range(n)]
    r = list(range(n));r[0],r[2]=2,0
    old = [S[r[x]] for x in range(n)]
    lifted = [0]*(m*n)
    for x,t in product(range(n),range(m)):
        y = r[x] if t==0 and x in (0,2,4) else x
        lifted[x*m+t] = S[y]*m+(t+(y==1))%m
    a = sorted(map(len,cycles(old)))
    b = sorted(map(len,cycles(lifted)))
    require(a==[2,4] and b==[4,20], 'roof counterexample')
    return {'base_lengths':a,'lifted_lengths':b,'uniform_rescaling':False}

def main(out):
    core_cases=[];arc_observations=0
    for m in range(4,41,2):
        _,C,V = physical_factors(m,lambda v:near_row(m,v),(1,1,1))
        require([len(c) for c in C]==[1,1,2], 'near core circuit counts')
        require(sorted(map(len,C[2]))==[m**3//2]*2,'defect cycle lengths')
        require({frozenset(defect_label(m,V[v]) for v in c) for c in C[2]} ==
                {frozenset([0]),frozenset([1])}, 'defect label not exact')
        _,H,_ = physical_factors(m,lambda v:terminal_row(m,v),(1,1,1))
        require(all(len(c)==1 for c in H),'terminal core is not Hamilton')
        anchors=[(0,1,0),(1,1,0),(0,0,0),(0,m-2,3)]
        require(all(near_row(m,v)==terminal_row(m,v) for v in anchors),'anchor mismatch')
        changed=sum(near_row(m,v)!=terminal_row(m,v) for v in V)
        require(changed==m**3-m*m-4*m+7,'difference support formula')
        core_cases.append({'m':m,'changed_sources':changed})
        arc_observations+=6*m**3
    shell_cases=[]
    for m,p in product((4,6,8,10),(4,5,7)):
        k=p//2
        _,C,_=physical_factors(m,lambda v:shell_row(m,p,sum(v)%m,v[2]),(p-k,k,p))
        require(all(len(c)==1 for c in C),'shell not Hamilton')
        shell_cases.append([m,2*p+3])
        arc_observations+=2*p*m**3
    inc=[]
    for m,p in product((4,6,8,12,16,20),range(4,33)):
        incidence_check(m,p);inc.append([m,p])
    app=[]
    for m in range(4,201,2):
        size,visits=appendix_check(m)
        app.append({'m':m,'Q_size':size,'translation_gap_roof_sum':visits})
    report={
      'scope':'Finite transcription checks for the self-contained manuscript; not an all-parameter or formal proof.',
      'implementation':'Standalone standard-library checker; no retained constructor imported.',
      'core_parameters':core_cases,
      'shell_parameters_m_d':shell_cases,
      'near_and_terminal_coloured_arc_observations':arc_observations,
      'seed_and_residual_incidence_cases':len(inc),
      'incidence_moduli':[4,6,8,12,16,20],
      'incidence_p_inclusive':[4,32],
      'appendix_cases':app,
      'length_counterexample':length_counterexample(),
      'new_full_high_dimensional_dense_audit':False,
      'proof_assistant_used':False,
      'all_checks_passed':True}
    Path(out).write_text(json.dumps(report,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:report[k] for k in ('near_and_terminal_coloured_arc_observations',
                                         'seed_and_residual_incidence_cases','all_checks_passed')},indent=2))
    print(f'Core moduli: {len(core_cases)}; shell examples: {len(shell_cases)}; appendix moduli: {len(app)}.')

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out',default=str(Path(__file__).with_name('MANUSCRIPT_CHECK_REPORT.json')))
    args=parser.parse_args()
    main(args.out)
