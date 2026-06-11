#!/usr/bin/env python3
"""Audit the D9 anchor candidate for the pair-row tail--head active identity.

This is stricter than terminal tree/coforest support verification.  For a pair
part P={a,b}, a single rank-one active support edge e must give descendant
coordinate +1 on the physical row increment for both affected chronological
colors, after contracting the previously built color forest and rooting at that
color.  The script lists, for each pair part, whether the existing support forest
contains such a common active edge.
"""
import json
from pathlib import Path
D = 9
path = Path('/mnt/data/d9_anchor_candidate.json')
cert = json.loads(path.read_text())
shifts = cert['shifts']

def norm(e):
    a,b = e
    return tuple(sorted((a,b)))

def row_perm(row):
    p = list(range(D))
    a,b,c = row['triple']
    p[a]=b; p[b]=c; p[c]=a
    for x,y in row['pairs']:
        p[x]=y; p[y]=x
    return p
perms = [row_perm(r) for r in cert['rows_shifted']]

# previous global color forests, exactly as in verify_d9_anchor_candidate.py
prev = [[[] for _ in range(D)] for __ in range(D)]
for color in range(D):
    edges=[]
    for r,(s,p) in enumerate(zip(shifts,perms)):
        prev[color][r] = list(edges)
        tail = (color+s) % D
        head = p[tail]
        edges.append(norm((tail, head)))
    prev[color][D-2] = list(edges)

def dsu(n, edges):
    parent = list(range(n))
    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x
    def union(a,b):
        ra,rb = find(a), find(b)
        if ra != rb:
            parent[rb] = ra
    for a,b in edges:
        union(a,b)
    return find

def quotient(color, stage):
    find0 = dsu(D, prev[color][stage])
    roots = sorted({find0(x) for x in range(D)})
    idx = {root:i for i,root in enumerate(roots)}
    comp = [idx[find0(x)] for x in range(D)]
    return comp, len(roots), comp[color]

def lambda_value(color, stage, support_edges, active_edge, delta):
    comp,n,root = quotient(color, stage)
    se = norm((comp[active_edge[0]], comp[active_edge[1]]))
    if se[0] == se[1]:
        return None
    qedges=[]
    for a,b in support_edges:
        qe = norm((comp[a], comp[b]))
        if qe[0] != qe[1]:
            qedges.append(qe)
    if se not in qedges:
        return None
    adj=[set() for _ in range(n)]
    removed=False
    for qe in qedges:
        if qe == se and not removed:
            removed=True
            continue
        a,b=qe
        adj[a].add(b); adj[b].add(a)
    seen={root}; stack=[root]
    while stack:
        u=stack.pop()
        for v in adj[u]:
            if v not in seen:
                seen.add(v); stack.append(v)
    desc=set(range(n))-seen
    tail,head=delta
    return (1 if comp[head] in desc else 0) - (1 if comp[tail] in desc else 0)

fail=[]
print('D9 pair active-identity audit')
for r,(s,p,supp) in enumerate(zip(shifts,perms,cert['supports_unshifted'])):
    for item in supp['parts']:
        P=item['P']
        if len(P) != 2:
            continue
        M=[norm(e) for e in item['M']]
        good=[]
        table=[]
        for e in M:
            vals=[]
            for c in P:
                tail=(c+s)%D
                head=p[tail]
                vals.append(lambda_value(c,r,M,e,(tail,head)))
            table.append((e, vals))
            if vals == [1,1]:
                good.append(e)
        status='PASS' if good else 'FAIL'
        if not good:
            fail.append((r+1,P,table))
        print(f'stage {r+1}, P={P}: {status}; common +1 active edges: {good}')
print(f'pair parts failing common +1 active-edge test: {len(fail)}')
