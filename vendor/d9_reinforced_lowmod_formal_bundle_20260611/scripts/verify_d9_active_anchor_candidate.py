#!/usr/bin/env python3
"""
Verify the D=9 active-anchor graph certificate.

Checks:
  (1) stage rows are one 3-cycle plus a matching of three pairs;
  (2) final color forests are one-isolate trees and closing edges make trees;
  (3) every listed support is a simultaneous rooted coforest completion;
  (4) every pair row has its physical pair edge in the support and descendant
      increment ±1 for the two affected colors;
  (5) triple rows at stages 1--6 have two active support edges, all other
      support coordinates vanish on the three physical increments, and the
      three active vectors are A2-primitive, i.e. every pair has determinant ±1;
  (6) the stage-7 triple is the terminal shifted triple (t,0,1), here (6,0,1),
      and has rooted-coforest support.  Terminal A2 cyclicity is the separate
      uniform terminal-block lemma, not re-proved by this graph script.
"""
import json, sys, collections
from pathlib import Path

path = Path(sys.argv[1]) if len(sys.argv) > 1 else Path('/mnt/data/d9_active_anchor_candidate_v1.json')
cert = json.loads(path.read_text())
D = cert['D']
assert D == 9
shifts = cert['shifts']
rows = cert['rows_shifted']
supports = cert['supports_unshifted']
assert len(shifts) == D-2 == len(rows) == len(supports)
assert len(set(shifts)) == len(shifts)

def norm(e):
    a,b = e
    assert 0 <= a < D and 0 <= b < D and a != b
    return (a,b) if a < b else (b,a)

def dsu(n):
    parent=list(range(n)); size=[1]*n
    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]; x = parent[x]
        return x
    def union(a,b):
        ra,rb = find(a),find(b)
        if ra == rb: return False
        if size[ra] < size[rb]: ra,rb = rb,ra
        parent[rb] = ra; size[ra] += size[rb]
        return True
    return parent,size,find,union

def components_from_edges(edges, n=D, require_forest=True):
    parent,size,find,union = dsu(n)
    for e in edges:
        a,b=e
        ok = union(a,b)
        if require_forest and not ok:
            raise AssertionError(f'cycle in forest at edge {e}; edges={edges}')
    comp=collections.defaultdict(list)
    for x in range(n): comp[find(x)].append(x)
    return list(comp.values()), find

def row_perm(row):
    used=[]; p=list(range(D))
    tri=row['triple']; pairs=row['pairs']
    assert len(tri)==3 and len(set(tri))==3
    a,b,c=tri; p[a]=b; p[b]=c; p[c]=a; used += tri
    assert len(pairs)==3
    for x,y in pairs:
        assert x != y
        p[x]=y; p[y]=x; used += [x,y]
    assert sorted(used) == list(range(D)), f'row not a triple+matching partition: {row}'
    return tuple(p)
perms=[row_perm(r) for r in rows]

def prev_edges(color, upto):
    edges=[]
    for r in range(upto):
        s=shifts[r]; p=perms[r]
        tail=(color+s)%D; head=p[tail]
        edges.append(norm((tail,head)))
    return edges

def qdata(color, stage):
    comps, find = components_from_edges(prev_edges(color,stage))
    roots=sorted({find(x) for x in range(D)})
    idx={rt:i for i,rt in enumerate(roots)}
    comp=[idx[find(x)] for x in range(D)]
    return comp, len(roots), comp[color]

def comp_edge(comp,e):
    a,b=e; ia,ib=comp[a],comp[b]
    if ia == ib: return None
    return (ia,ib) if ia < ib else (ib,ia)

def support_basic(stage, P, M):
    R = D - (stage + 1) - 1
    M=[norm(e) for e in M]
    assert len(M)==R and len(set(M))==R, f'bad support size stage {stage+1}, P={P}, M={M}, want {R}'
    for color in P:
        comp,n,root = qdata(color, stage)
        parent,size,find,union = dsu(n)
        seen=set()
        for e in M:
            qe=comp_edge(comp,e)
            assert qe is not None, f'internal support edge stage {stage+1}, color {color}, edge {e}'
            assert qe not in seen, f'duplicate quotient support edge stage {stage+1}, color {color}, edge {e}'
            seen.add(qe)
            assert union(*qe), f'cycle in quotient support stage {stage+1}, color {color}, edge {e}'
        qcomps=collections.defaultdict(list)
        for i in range(n): qcomps[find(i)].append(i)
        sizes=sorted(len(v) for v in qcomps.values())
        assert sizes == [1,n-1], f'not tree-on-all-but-one stage {stage+1}, P={P}, color={color}, sizes={sizes}'
        big=[v for v in qcomps.values() if len(v)==n-1][0]
        assert root in big, f'root component missing stage {stage+1}, P={P}, color={color}'
    return True

def lam(stage, color, M, e, delta):
    comp,n,root=qdata(color,stage)
    se=comp_edge(comp,e)
    assert se is not None, f'active edge internal for color {color}: {e}'
    adj=[set() for _ in range(n)]; removed=False
    for f in M:
        qe=comp_edge(comp,f)
        assert qe is not None
        if qe == se and not removed:
            removed=True
            continue
        adj[qe[0]].add(qe[1]); adj[qe[1]].add(qe[0])
    assert removed, f'active edge {e} not in support'
    seen={root}; stack=[root]
    while stack:
        u=stack.pop()
        for v in adj[u]:
            if v not in seen:
                seen.add(v); stack.append(v)
    desc=set(range(n))-seen
    t,h=delta
    return int(comp[h] in desc) - int(comp[t] in desc)

def det(v,w): return v[0]*w[1]-v[1]*w[0]

# final color forests
forests=[]
for color in range(D):
    edges=[]
    for r,(s,p) in enumerate(zip(shifts,perms)):
        tail=(color+s)%D; head=p[tail]
        e=norm((tail,head))
        assert e not in edges, f'duplicate final edge for color {color}: {e}'
        edges.append(e)
    comps,_=components_from_edges(edges)
    sizes=sorted([len(c) for c in comps], reverse=True)
    assert sizes == [D-1,1], f'color {color} not one-isolate: sizes={sizes}, edges={edges}'
    iso=[c[0] for c in comps if len(c)==1][0]
    assert iso != color, f'closing edge loops for color {color}'
    components_from_edges(edges+[norm((iso,color))])
    forests.append((edges,iso))

# support and active checks
for stage,(row,srow) in enumerate(zip(rows,supports)):
    s=shifts[stage]; p=perms[stage]
    expected_parts=[tuple((x-s)%D for x in row['triple'])] + [tuple((x-s)%D for x in pair) for pair in row['pairs']]
    got_parts=[tuple(item['P']) for item in srow['parts']]
    assert got_parts == expected_parts, f'parts mismatch stage {stage+1}: got {got_parts}, expected {expected_parts}'
    # basic support for all parts
    for item in srow['parts']:
        support_basic(stage, item['P'], [norm(e) for e in item['M']])
    # active conditions
    triP=expected_parts[0]
    triM=[norm(e) for e in srow['parts'][0]['M']]
    if stage <= 5:
        found=False; witness=None
        deltas={c:((c+s)%D,p[(c+s)%D]) for c in triP}
        for i,e1 in enumerate(triM):
            for e2 in triM[i+1:]:
                vecs=[]; ok=True
                for c in triP:
                    vals={e:lam(stage,c,triM,e,deltas[c]) for e in triM}
                    if any(v != 0 for e,v in vals.items() if e not in (e1,e2)):
                        ok=False; break
                    v=(vals[e1], vals[e2])
                    if v == (0,0) or any(x not in (-1,0,1) for x in v):
                        ok=False; break
                    vecs.append(v)
                if ok and all(abs(det(vecs[a],vecs[b]))==1 for a in range(3) for b in range(a+1,3)):
                    found=True; witness=(e1,e2,vecs); break
            if found: break
        assert found, f'no active A2 triple witness stage {stage+1}, P={triP}'
    else:
        assert tuple(row['triple'][1:]) == (0,1), f'terminal triple is not (t,0,1): {row["triple"]}'
    # pair active unit
    for pair,item in zip(row['pairs'], srow['parts'][1:]):
        M=[norm(e) for e in item['M']]
        e=norm(pair)
        assert e in M, f'physical pair edge {e} absent from support stage {stage+1}, P={item["P"]}'
        P=tuple(item['P'])
        deltas={c:((c+s)%D,p[(c+s)%D]) for c in P}
        vals=[lam(stage,c,M,e,deltas[c]) for c in P]
        assert all(v in (-1,1) for v in vals), f'non-unit pair values stage {stage+1}, pair {pair}, P={P}: {vals}'

print('OK: D9 active-anchor graph certificate verified')
print('rows_shifted:')
for r,row in enumerate(rows,1):
    print(f'  {r}: triple {tuple(row["triple"])} pairs {[tuple(p) for p in row["pairs"]]} shift {shifts[r-1]}')
print('color forests:')
for c,(edges,iso) in enumerate(forests):
    print(f'  color {c}: isolate {iso}, closing {iso}->{c}, edges ' + ','.join(f'{a}{b}' for a,b in edges))
