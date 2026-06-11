#!/usr/bin/env python3
"""Formalization-oriented finite verifier for the D9 low moduli m=4,6,8.

This is deliberately stronger than the placement-only verifier.  It still does
not expand the full root-flat return permutations, but it turns every local
low-modulus placement hypothesis used by the signed D9 anchor-realization
criterion into finite set equalities inside K_{9,m}.

Checked for each m in {4,6,8}:
  * all splice supports, terminal carrier, and reserve plane are explicit finite
    affine cosets in K_{9,m} with the expected cardinalities;
  * supports are closed under their listed active directions;
  * after contracting the previous color forest, each support maps onto the
    required active quotient line/plane, while inactive and omitted coordinates
    are constant, checked by enumerating the whole support set;
  * pair active increments are exactly ±1; triple active determinant packets are
    exactly ±1;
  * supports with the same folded height are disjoint;
  * terminal and reserve planes are disjoint from all splice supports and from
    each other;
  * the terminal A2 word has one m^2-cycle for each terminal color, and the
    marked comparison cycle embeds in the terminal carrier;
  * the ordered 12 endpoint reserve sites have the semantic roles required by
    the endpoint-reserve interface and avoid the protected terminal carrier and
    all splice supports.
"""
import json, collections, itertools, math
from pathlib import Path

D=9
ROOT=Path(__file__).resolve().parents[1]
ACTIVE=ROOT/'certificates'/'d9_active_anchor_candidate_v1.json'
LOW=ROOT/'certificates'/'d9_lowmod_finite_placement_semantic.json'
TERM=ROOT/'certificates'/'d9_terminal_reserve_frame_candidate.json'
OUT=ROOT/'verification'/'d9_lowmod_formal_semantics_verification.txt'

cert=json.loads(ACTIVE.read_text())
low=json.loads(LOW.read_text())
term=json.loads(TERM.read_text())
shifts=cert['shifts']; rows=cert['rows_shifted']; supports=cert['supports_unshifted']

ROLES=['U0','U1','U2']+[f'U{j}_c' for j in range(1,9)]+['U_star']
PURPOSE={r:('terminal_exchange' if r in ('U0','U1','U2') else 'next_reserve' if r=='U_star' else 'coordinate_renewal') for r in ROLES}

def fail(msg):
    raise AssertionError(msg)
def assert_true(cond,msg):
    if not cond: fail(msg)

def norm(e):
    if isinstance(e,str):
        # edge names in this bundle are two decimal digits, labels 0..8.
        e=(int(e[0]),int(e[1]))
    a,b=e
    return (a,b) if a<b else (b,a)
def edge_word(e):
    a,b=norm(e); return f'{a}{b}'
def edge_vec(e,m=None,raw=False):
    if isinstance(e,str): a=int(e[0]); b=int(e[1])
    else: a,b=e
    v=[0]*D; v[a]-=1; v[b]+=1
    if m is not None and not raw: v=[x%m for x in v]
    return tuple(v)
def add(u,v,m): return tuple((u[i]+v[i])%m for i in range(D))
def smul(k,u,m): return tuple((k*u[i])%m for i in range(D))
def span(edges,m):
    S={tuple([0]*D)}
    for e in edges:
        d=edge_vec(e,m)
        S={add(s,smul(k,d,m),m) for s in S for k in range(m)}
    return S
def coset(base,edges,m):
    b=tuple(x%m for x in base)
    S=span(edges,m)
    return {add(b,s,m) for s in S}, S

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

def coforest_contract_summary(color, stage, M):
    M=[norm(x) for x in M]
    comp, comps, root = comp_data(color,stage)
    n=len(comps)
    par,sz,find,union=dsu(n)
    contracted=[]
    for f in M:
        q=comp_edge(comp,f)
        assert_true(q is not None, f'color {color} stage {stage+1}: support edge {edge_word(f)} internal after contraction')
        assert_true(union(*q), f'color {color} stage {stage+1}: contracted support has cycle at {edge_word(f)}')
        contracted.append(q)
    blocks=collections.defaultdict(list)
    for i in range(n): blocks[find(i)].append(i)
    tree_blocks=[v for v in blocks.values() if len(v)>1]
    omitted=[v[0] for v in blocks.values() if len(v)==1]
    assert_true(len(tree_blocks)==1, f'color {color} stage {stage+1}: support not one tree plus isolates: {list(blocks.values())}')
    assert_true(root in tree_blocks[0], f'color {color} stage {stage+1}: rooted support tree misses root component')
    assert_true(len(omitted)==1, f'color {color} stage {stage+1}: expected exactly one omitted component, got {omitted}')
    # Edges in a tree on |tree| components.
    assert_true(len(contracted)==len(tree_blocks[0])-1, f'color {color} stage {stage+1}: contracted support size mismatch')
    return comp, comps, root, omitted[0]

def desc_labels(color, stage, M, e):
    M=[norm(x) for x in M]; e=norm(e)
    comp, comps, root, _ = coforest_contract_summary(color,stage,M)
    n=len(comps); se=comp_edge(comp,e)
    assert_true(se is not None, f'edge {edge_word(e)} internal for color {color} at stage {stage+1}')
    adj=[set() for _ in range(n)]; removed=False
    for f in M:
        q=comp_edge(comp,f)
        if q==se and not removed:
            removed=True; continue
        adj[q[0]].add(q[1]); adj[q[1]].add(q[0])
    assert_true(removed, f'edge {edge_word(e)} not in support')
    seen={root}; st=[root]
    while st:
        u=st.pop()
        for v in adj[u]:
            if v not in seen:
                seen.add(v); st.append(v)
    desc_comps=set(range(n))-seen
    return [j for j,co in enumerate(comp) if co in desc_comps]

def omitted_labels(color, stage, M):
    comp, comps, root, omitted = coforest_contract_summary(color,stage,M)
    return [j for j,co in enumerate(comp) if co==omitted]

def active_edges(stage, part_index, item):
    if part_index==0:
        if stage<=5: # stages 0..5 are non-terminal triples; stage 6 terminal uses item M as basic support here
            return [norm(e) for e in cert['active_data'][stage]['parts'][0]['active_edges']]
        return [norm(e) for e in item['M']]
    return [norm(rows[stage]['pairs'][part_index-1])]

def dot_labels(v,labels,m=None):
    s=sum(v[i] for i in labels)
    return s if m is None else s%m

def det2(a,b): return a[0]*b[1]-a[1]*b[0]
def is_unit(x,m): return math.gcd(x%m,m)==1

def active_coords(point, color, stage, M, A, m):
    return tuple(dot_labels(point, desc_labels(color,stage,M,a), m) for a in A)
def inactive_coords(point, color, stage, M, A, m):
    Aset={norm(a) for a in A}
    return tuple((edge_word(f), dot_labels(point, desc_labels(color,stage,M,f), m)) for f in [norm(x) for x in M] if norm(f) not in Aset)
def omitted_coord(point, color, stage, M, m):
    return dot_labels(point, omitted_labels(color,stage,M), m)

# Terminal A2 model from reinforced verifier.
def add2(a,b,m): return ((a[0]+b[0])%m,(a[1]+b[1])%m)
def sub2(a,b,m): return ((a[0]-b[0])%m,(a[1]-b[1])%m)
a2=[(1,0),(0,1),(0,0)]
p2=(1,2)
words={'id': (0,1,2),'tau02': (2,1,0),'tau12': (0,2,1),'tau01': (1,0,2),'chi+': (1,2,0),'chi-': (2,0,1)}
Deltas=[(0,1),(1,0),(1,-1)]
def omega(q,m):
    x,y=q
    if (x%m,y%m)==(p2[0]%m,p2[1]%m): return words['id']
    if y%m==p2[1]%m:
        t=(x-p2[0])%m
        if t==1%m: return words['chi+']
        if t==(-1)%m: return words['chi-']
        if t!=0: return words['tau02']
    if x%m==p2[0]%m:
        t=(y-p2[1])%m
        if t==1%m: return words['chi-']
        if t==(-1)%m: return words['chi+']
        if t!=0: return words['tau12']
    if (x+y-p2[0]-p2[1])%m==0:
        t=(y-p2[1])%m
        if t==1%m: return words['chi+']
        if t==(-1)%m: return words['chi-']
        if t!=0: return words['tau01']
    return words['id']
def eta(i,z,m):
    q=sub2(z,a2[i],m); w=omega(q,m)
    return add2(q,a2[w[i]],m)
def Fterm(i,z,m): return eta(i,add2(z,Deltas[i],m),m)
def orbit_len2(f,start,m):
    seen=[]; z=start
    while z not in seen:
        seen.append(z); z=f(z)
    return len(seen), z, seen
def terminal_selector_C(m):
    if m==4: return [(0,3),(3,0),(3,3)], (1,2)
    L=m-1; C=[None]*L
    C[0]=(0,0); C[1]=((-1)%m,1%m)
    for j in range(2,L): C[j]=((-j-1)%m,j%m)
    return C,(0,1)
def embed_terminal(q,base,edges,m):
    b=tuple(x%m for x in base); e0=edge_vec(edges[0],m); e1=edge_vec(edges[1],m)
    return add(add(b,smul(q[0],e0,m),m),smul(q[1],e1,m),m)

logs=[]
formal_facts={'D':D,'description':'Finite low-modulus formal semantic facts for D9, generated by verify_d9_lowmod_formal_semantics.py','moduli':{}}
expected_count=sum(len(st['parts']) for st in supports)
for m_str,data in sorted(low['moduli'].items(), key=lambda kv:int(kv[0])):
    m=int(m_str)
    finite={(o['stage']-1,o['part_index']):o for o in data['splice_supports']}
    assert_true(len(finite)==expected_count, f'm={m}: wrong splice support count')
    objects=[]; support_facts=[]
    for stage,st in enumerate(supports):
        for pi,item in enumerate(st['parts']):
            o=finite[(stage,pi)]
            P=item['P']; M=[norm(e) for e in item['M']]; A=active_edges(stage,pi,item)
            assert_true(o['P']==P, f'm={m} {o["name"]}: P mismatch')
            assert_true(sorted(o['edges'])==sorted(edge_word(e) for e in A), f'm={m} {o["name"]}: active edge mismatch')
            base=tuple(x%m for x in o['base'])
            assert_true(sum(base)%m==0, f'm={m} {o["name"]}: base not in K')
            C,S=coset(base,o['edges'],m)
            rank=2 if pi==0 else 1
            if pi==0 and stage==6: rank=len(o['edges'])  # terminal basic support is not a non-terminal splice, but still explicit.
            assert_true(len(S)==m**len(o['edges']), f'm={m} {o["name"]}: span has unexpected kernel, got {len(S)}, edges={o["edges"]}')
            assert_true(len(C)==len(S), f'm={m} {o["name"]}: coset cardinal mismatch')
            if 'span_size' in o: assert_true(o['span_size']==len(S), f'm={m} {o["name"]}: recorded span_size mismatch')
            # Direction closure, completely finite.
            for pnt in list(C):
                for aedge in A:
                    assert_true(add(pnt,edge_vec(aedge,m),m) in C, f'm={m} {o["name"]}: not closed under active edge {edge_word(aedge)}')
            per_color=[]
            for c in P:
                # Coforest contraction facts are recomputed.
                coforest_contract_summary(c,stage,M)
                # Full finite old-head quotient image facts.
                act_img={active_coords(pnt,c,stage,M,A,m) for pnt in C}
                inact_img={inactive_coords(pnt,c,stage,M,A,m) for pnt in C}
                om_img={omitted_coord(pnt,c,stage,M,m) for pnt in C}
                assert_true(len(inact_img)==1, f'm={m} {o["name"]} c={c}: inactive coords vary')
                assert_true(len(om_img)==1, f'm={m} {o["name"]} c={c}: omitted coord varies')
                assert_true(len(act_img)==m**len(A), f'm={m} {o["name"]} c={c}: active quotient image not full, got {len(act_img)}')
                # Tail-head active increment facts, as raw integers.
                s=shifts[stage]; p=perms[stage]
                tail=(c+s)%D; head=p[tail]
                inc=edge_vec((tail,head),raw=True)
                raw_vec=tuple(dot_labels(inc,desc_labels(c,stage,M,a),None) for a in A)
                per_color.append({'color':c,'tail':tail,'head':head,'raw_active_increment':raw_vec,'active_image_size':len(act_img)})
            if pi>0:
                for pc in per_color:
                    val=pc['raw_active_increment'][0]
                    assert_true(val in (-1,1), f'm={m} {o["name"]} c={pc["color"]}: pair increment {val} not ±1')
                    assert_true(is_unit(val,m), f'm={m} {o["name"]}: pair increment not unit')
            elif stage<=5:
                vecs=[pc['raw_active_increment'] for pc in per_color]
                for x,y in itertools.combinations(vecs,2):
                    d=det2(x,y)
                    assert_true(d in (-1,1), f'm={m} {o["name"]}: triple det {d} for {x},{y} not ±1')
                    assert_true(is_unit(d,m), f'm={m} {o["name"]}: triple determinant not unit')
            objects.append({'name':o['name'],'height':o['height']%m,'set':C,'size':len(C)})
            support_facts.append({'name':o['name'],'stage':stage+1,'part_index':pi,'P':P,'height_mod_m':o['height']%m,'support_size':len(C),'active_edges':[edge_word(e) for e in A],'per_color':per_color})
    # Folded-height separation.
    byh=collections.defaultdict(list)
    for obj in objects: byh[obj['height']].append(obj)
    height_union_sizes={}
    for h,grp in byh.items():
        U=set(); sumsz=0
        for a,b in itertools.combinations(grp,2):
            inter=a['set']&b['set']
            assert_true(not inter, f'm={m}: splice collision at folded height {h}: {a["name"]} vs {b["name"]}, size {len(inter)}')
        for g in grp:
            U |= g['set']; sumsz += g['size']
        assert_true(len(U)==sumsz, f'm={m}: union size mismatch at height {h}')
        height_union_sizes[str(h)]={'number_of_supports':len(grp),'union_size':len(U)}
    # Terminal and reserve finite sets.
    T=data['terminal_carrier']; R=data['reserve_plane']
    Tset,TS=coset(tuple(x%m for x in T['base']),T['edges'],m)
    Rset,RS=coset(tuple(x%m for x in R['base']),R['edges'],m)
    assert_true(len(TS)==m*m and len(Tset)==m*m, f'm={m}: terminal carrier not rank 2')
    assert_true(len(RS)==m*m and len(Rset)==m*m, f'm={m}: reserve plane not rank 2')
    assert_true(Tset.isdisjoint(Rset), f'm={m}: terminal/reserve collision')
    for obj in objects:
        assert_true(Tset.isdisjoint(obj['set']), f'm={m}: terminal hits {obj["name"]}')
        assert_true(Rset.isdisjoint(obj['set']), f'm={m}: reserve hits {obj["name"]}')
    # Terminal A2 finite cycles and marked comparison cycle embedded in carrier.
    for i in range(3):
        n,end,orb=orbit_len2(lambda z,i=i:Fterm(i,z,m),(0,0),m)
        assert_true(n==m*m and end==(0,0) and len(set(orb))==m*m, f'm={m}: terminal F{i} not m^2-cycle')
    Csel,local_pair=terminal_selector_C(m)
    embedded=[embed_terminal(q,T['base'],T['edges'],m) for q in Csel]
    assert_true(len(set(embedded))==len(Csel), f'm={m}: marked comparison cycle collapses')
    assert_true(all(x in Tset for x in embedded), f'm={m}: marked comparison cycle not in carrier')
    # Reserve semantic roles and membership.
    sites=data['reserve_sites']
    assert_true([s['name'] for s in sites]==ROLES, f'm={m}: reserve role order mismatch')
    seen=set()
    for site in sites:
        assert_true(site.get('role')==site['name'], f'm={m}: reserve site role mismatch {site}')
        assert_true(site.get('purpose')==PURPOSE[site['name']], f'm={m}: reserve site purpose mismatch {site}')
        pnt=tuple(site['point'])
        assert_true(sum(pnt)%m==0, f'm={m}: reserve site {site["name"]} not root-flat')
        assert_true(pnt in Rset, f'm={m}: reserve site {site["name"]} not in reserve plane')
        assert_true(pnt not in Tset, f'm={m}: reserve site {site["name"]} in protected terminal carrier')
        for obj in objects:
            assert_true(pnt not in obj['set'], f'm={m}: reserve site {site["name"]} in splice {obj["name"]}')
        seen.add(pnt)
    assert_true(len(seen)==12, f'm={m}: reserve sites not distinct')
    formal_facts['moduli'][str(m)]={'support_count':len(objects),'terminal_carrier_size':len(Tset),'reserve_plane_size':len(Rset),'reserve_site_count':len(seen),'folded_height_unions':height_union_sizes,'supports':support_facts}
    logs.append(f'm={m}: formal finite semantics OK; supports={len(objects)}, terminal={len(Tset)}, reserve={len(Rset)}, reserve_sites={len(seen)}, folded_heights={sorted(byh)}')

OUT.parent.mkdir(exist_ok=True)
OUT.write_text('OK: D9 low-modulus formal finite semantics verified\n'+'\n'.join(logs)+'\n')
(ROOT/'verification'/'d9_lowmod_formal_facts.json').write_text(json.dumps(formal_facts,indent=2,sort_keys=True))
print(OUT.read_text(), end='')
