#!/usr/bin/env python3
"""Verify finite low-modulus D9 placement ledgers for m=4,6,8.

This script verifies only the finite placement layer. It relies on the active
D9 anchor data for the quotient/coforest witnesses.
"""
import json, collections, itertools, math
from pathlib import Path
D=9
ROOT=Path(__file__).resolve().parents[1]
ACTIVE=ROOT/'certificates'/'d9_active_anchor_candidate_v1.json'
LOW=ROOT/'certificates'/'d9_lowmod_finite_placement_candidate.json'
OUT=ROOT/'verification'/'d9_lowmod_finite_placement_verification.txt'
cert=json.loads(ACTIVE.read_text())
low=json.loads(LOW.read_text())
shifts=cert['shifts']; rows=cert['rows_shifted']; supports=cert['supports_unshifted']

def norm(e):
    if isinstance(e,str): e=(int(e[0]),int(e[1]))
    a,b=e; return (a,b) if a<b else (b,a)
def edge_word(e):
    a,b=norm(e); return f'{a}{b}'
def edge_vec(e,m):
    if isinstance(e,str): a=int(e[0]); b=int(e[1])
    else: a,b=e
    v=[0]*D; v[a]-=1; v[b]+=1
    return tuple(x%m for x in v)
def add(u,v,m): return tuple((u[i]+v[i])%m for i in range(D))
def smul(k,u,m): return tuple((k*u[i])%m for i in range(D))
def dot_label_sum(v,labels,m): return sum(v[i] for i in labels)%m

def span(edges,m):
    S={tuple([0]*D)}
    for e in edges:
        d=edge_vec(e,m)
        multiples=[smul(k,d,m) for k in range(m)]
        S={add(s,md,m) for s in S for md in multiples}
    return S
def coset(base,edges,m):
    S=span(edges,m)
    return {add(base,s,m) for s in S}, S

def row_perm(row):
    p=list(range(D))
    a,b,c=row['triple']; p[a]=b; p[b]=c; p[c]=a
    for x,y in row['pairs']:
        p[x]=y; p[y]=x
    return tuple(p)
perms=[row_perm(r) for r in rows]

def dsu(n):
    par=list(range(n)); sz=[1]*n
    def find(x):
        while par[x]!=x:
            par[x]=par[par[x]]; x=par[x]
        return x
    def union(a,b):
        ra,rb=find(a),find(b)
        if ra==rb: return False
        if sz[ra]<sz[rb]: ra,rb=rb,ra
        par[rb]=ra; sz[ra]+=sz[rb]
        return True
    return par,sz,find,union

def prev_edges(color, upto):
    edges=[]
    for r in range(upto):
        s=shifts[r]; p=perms[r]
        tail=(color+s)%D; head=p[tail]
        edges.append(norm((tail,head)))
    return edges

def comp_data(color, stage):
    par,sz,find,union=dsu(D)
    for e in prev_edges(color,stage): union(*e)
    roots=sorted({find(i) for i in range(D)})
    idx={rt:i for i,rt in enumerate(roots)}
    comp=[idx[find(i)] for i in range(D)]
    comps=[[] for _ in roots]
    for i,c in enumerate(comp): comps[c].append(i)
    return comp, comps, comp[color]

def comp_edge(comp,e):
    a,b=norm(e); ia,ib=comp[a],comp[b]
    if ia==ib: return None
    return norm((ia,ib))

def desc_labels(color, stage, M, e):
    M=[norm(x) for x in M]; e=norm(e)
    comp, comps, root = comp_data(color,stage)
    n=len(comps); se=comp_edge(comp,e)
    if se is None: raise AssertionError(f'edge {edge_word(e)} internal for color {color} at stage {stage+1}')
    adj=[set() for _ in range(n)]; removed=False
    for f in M:
        q=comp_edge(comp,f)
        if q is None: raise AssertionError('internal support edge')
        if q==se and not removed:
            removed=True; continue
        adj[q[0]].add(q[1]); adj[q[1]].add(q[0])
    if not removed: raise AssertionError('edge not in support')
    seen={root}; st=[root]
    while st:
        u=st.pop()
        for v in adj[u]:
            if v not in seen:
                seen.add(v); st.append(v)
    desc_comps=set(range(n))-seen
    return [j for j,co in enumerate(comp) if co in desc_comps]

def omitted_labels(color, stage, M):
    M=[norm(x) for x in M]
    comp, comps, root=comp_data(color,stage)
    n=len(comps); par,sz,find,union=dsu(n)
    for f in M:
        q=comp_edge(comp,f)
        if q is None: raise AssertionError('internal support edge')
        if not union(*q): raise AssertionError('cycle in support')
    blocks=collections.defaultdict(list)
    for i in range(n): blocks[find(i)].append(i)
    omitted=[v[0] for v in blocks.values() if len(v)==1]
    if len(omitted)!=1: raise AssertionError('not exactly one omitted comp')
    oc=omitted[0]
    return [j for j,co in enumerate(comp) if co==oc]

def active_edges(stage, part_index, item):
    if part_index==0:
        if stage<=5:
            return [norm(e) for e in cert['active_data'][stage]['parts'][0]['active_edges']]
        else:
            return [norm(e) for e in item['M']]
    else:
        return [norm(rows[stage]['pairs'][part_index-1])]

def det2(a,b): return a[0]*b[1]-a[1]*b[0]

def gcd_unit(x,m): return math.gcd(x%m,m)==1

logs=[]
# base active/coforest sanity via expected support list
for m_str,data in low['moduli'].items():
    m=int(m_str)
    objects=[]
    # index finite entries
    finite={(o['stage']-1,o['part_index']):o for o in data['splice_supports']}
    assert len(finite)==sum(len(st['parts']) for st in supports)
    for stage,st in enumerate(supports):
        for pi,item in enumerate(st['parts']):
            o=finite[(stage,pi)]
            P=item['P']; M=[norm(e) for e in item['M']]; A=active_edges(stage,pi,item)
            assert o['P']==P
            assert sorted(o['edges'])==sorted(edge_word(e) for e in A), (m,stage+1,pi,o['edges'],A)
            b=tuple(x%m for x in o['base'])
            assert sum(b)%m==0, (m,o['name'],'base not root-flat')
            C,S=coset(b,o['edges'],m)
            # expected rank sizes: pair m, nonterminal triple m^2, terminal support at least m or m^2 per edges listed
            if pi>0:
                assert len(S)==m, (m,o['name'],'pair span size',len(S))
            elif stage<=5:
                assert len(S)==m*m, (m,o['name'],'triple span size',len(S))
            # transversality and active units
            s=shifts[stage]; p=perms[stage]
            for c in P:
                tail=(c+s)%D; head=p[tail]
                inc=tuple((edge_vec((tail,head),m)[i]) for i in range(D))
                # inactive support coords vanish on active directions; omitted vanishes on active directions
                for f in M:
                    labels=desc_labels(c,stage,M,f)
                    vals=[dot_label_sum(edge_vec(a,m),labels,m) for a in A]
                    if f not in A:
                        assert all(v%m==0 for v in vals), (m,o['name'],c,edge_word(f),'inactive not const',vals)
                om=omitted_labels(c,stage,M)
                assert all(dot_label_sum(edge_vec(a,m),om,m)==0 for a in A), (m,o['name'],c,'omitted not const')
            # active vectors unit/primitive
            if pi>0:
                a=A[0]
                vals=[]
                for c in P:
                    tail=(c+s)%D; head=p[tail]
                    labels=desc_labels(c,stage,M,a)
                    val=sum(edge_vec((tail,head),m)[i] for i in labels)
                    vals.append(val)
                    assert gcd_unit(val,m), (m,o['name'],c,'nonunit pair active',val)
            elif stage<=5:
                vecs=[]
                for c in P:
                    tail=(c+s)%D; head=p[tail]
                    inc=edge_vec((tail,head),m)
                    vec=[sum(inc[i] for i in desc_labels(c,stage,M,a)) for a in A]
                    vecs.append(vec)
                for x,y in itertools.combinations(vecs,2):
                    assert gcd_unit(det2(x,y),m), (m,o['name'],'nonunit det',x,y,det2(x,y))
            objects.append({'name':o['name'],'height':o['height'],'base':b,'edges':o['edges'],'set':C,'span_size':len(S)})
    # splice separation for equal folded height
    byh=collections.defaultdict(list)
    for o in objects: byh[o['height']].append(o)
    intersections=0
    for h,grp in byh.items():
        for a,b in itertools.combinations(grp,2):
            inter=a['set']&b['set']
            assert not inter, (m,'splice collision',h,a['name'],b['name'],len(inter))
    # terminal/reserve plane
    T=data['terminal_carrier']; R=data['reserve_plane']
    Tb=tuple(x%m for x in T['base']); Rb=tuple(x%m for x in R['base'])
    assert sum(Tb)%m==0 and sum(Rb)%m==0
    Tset,TS=coset(Tb,T['edges'],m); Rset,RS=coset(Rb,R['edges'],m)
    assert len(TS)==m*m, (m,'terminal rank',len(TS))
    assert len(RS)==m*m, (m,'reserve rank',len(RS))
    assert Tset.isdisjoint(Rset), (m,'T/R collision')
    for o in objects:
        assert Tset.isdisjoint(o['set']), (m,'T collision',o['name'])
        assert Rset.isdisjoint(o['set']), (m,'R collision',o['name'])
    # reserve sites distinct and in plane
    dirs=[edge_vec(e,m) for e in R['edges']]
    seen=set()
    for site in data['reserve_sites']:
        a,b=site['coeff']; p=add(Rb, add(smul(a,dirs[0],m), smul(b,dirs[1],m),m),m)
        assert tuple(site['point'])==p, (m,'site mismatch',site['name'])
        assert sum(p)%m==0
        seen.add(p)
    assert len(seen)==12, (m,'reserve sites not distinct',len(seen))
    logs.append(f"m={m}: {len(objects)} splice supports verified; terminal size={len(Tset)} reserve size={len(Rset)}; reserve sites=12")

OUT.write_text('OK: D9 low-modulus finite placement verified\n'+'\n'.join(logs)+'\n')
print(OUT.read_text())
