#!/usr/bin/env python3
"""Build and verify a symbolic affine splice-placement ledger for the D9 active anchor.

This ledger covers the splice supports of the high-even D=9 anchor. It does not
claim terminal/reserve-plane separation or low-modulus RF2 instantiation.
"""
import json, collections, itertools, math
from pathlib import Path
from fractions import Fraction

D=9
ROOT=Path(__file__).resolve().parents[1]
SRC=ROOT/'certificates'/'d9_active_anchor_candidate_v1.json'
OUT=ROOT/'verification'/'generated_d9_affine_splice_placement_ledger.json'
TXT=ROOT/'verification'/'generated_d9_affine_splice_placement_verification.txt'
cert=json.loads(SRC.read_text())
shifts=cert['shifts']; rows=cert['rows_shifted']; supports=cert['supports_unshifted']

def norm(e):
    a,b=e; return (a,b) if a<b else (b,a)

def edge_word(e):
    a,b=norm(e); return f'{a}{b}'

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
    if se is None: raise AssertionError(f'edge {e} internal for color {color} at stage {stage+1}')
    adj=[set() for _ in range(n)]; removed=False
    for f in M:
        q=comp_edge(comp,f)
        if q is None: raise AssertionError('internal support edge')
        if q==se and not removed:
            removed=True; continue
        adj[q[0]].add(q[1]); adj[q[1]].add(q[0])
    if not removed: raise AssertionError('active edge not in support')
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
        if not union(*q): raise AssertionError('cycle')
    blocks=collections.defaultdict(list)
    for i in range(n): blocks[find(i)].append(i)
    omitted=[v[0] for v in blocks.values() if len(v)==1]
    if len(omitted)!=1: raise AssertionError(f'not one omitted comp: {blocks}')
    oc=omitted[0]
    return [j for j,co in enumerate(comp) if co==oc]

def edgevec(e):
    a,b=e; v=[0]*D; v[b]+=1; v[a]-=1; return v

def dot(a,b): return sum(x*y for x,y in zip(a,b))

def labels_vec(labels):
    v=[0]*D
    for i in labels: v[i]+=1
    return v

def active_edges(stage, part_index, item):
    if part_index==0:
        if stage<=5:
            return [norm(e) for e in cert['active_data'][stage]['parts'][0]['active_edges']]
        else:
            # Terminal triple is not a normal splice support; keep listed support only for terminal form.
            return [norm(e) for e in item['M']]
    else:
        return [norm(rows[stage]['pairs'][part_index-1])]

def active_graph_edges(stage):
    E=[]
    srow=supports[stage]
    for pi,item in enumerate(srow['parts']):
        E.extend(active_edges(stage,pi,item))
    return sorted(set(E))

def components_of_edges(edges):
    par,sz,find,union=dsu(D)
    for e in edges: union(*e)
    comps=collections.defaultdict(list)
    for i in range(D): comps[find(i)].append(i)
    return list(comps.values())

def primitive_band_function(edges):
    # Need w_i=w_j for all active edges, and gcd of coefficient differences 1.
    comps=components_of_edges(edges)
    # assign component values 0,1,2,... then center by subtracting min; this is primitive if at least 2 comps.
    w=[0]*D
    for val,comp in enumerate(comps):
        for i in comp: w[i]=val
    # normalize so min 0
    mn=min(w); w=[x-mn for x in w]
    g=0
    for i in range(D):
        for j in range(D):
            g=math.gcd(g, abs(w[i]-w[j]))
    if g!=1:
        # brute force assignments in [-2,2]
        for vals in itertools.product(range(-2,3), repeat=len(comps)):
            if len(set(vals))<2: continue
            ww=[0]*D
            for val,comp in zip(vals,comps):
                for i in comp: ww[i]=val
            g=0
            for i in range(D):
                for j in range(D): g=math.gcd(g, abs(ww[i]-ww[j]))
            if g==1:
                w=ww; break
        else: raise AssertionError('no primitive band functional')
    return w, comps

def solve_base_for_band(w, k):
    # Find integer x with sum x=0 and w.x=k.
    # Since gcd differences is 1, use pair i,j with w_i-w_j = ±1 if possible, else extended via brute small.
    for i in range(D):
        for j in range(D):
            if i!=j and w[i]-w[j] in (1,-1):
                diff=w[i]-w[j]
                x=[0]*D
                x[i]=k*diff  # if diff=-1, this gives -k, wdot = -k*w_i +? check below? use formula t(e_i-e_j), wdot=t(w_i-w_j)
                x[j]-=k*diff
                # wait sum zero and wdot = k*diff*(w_i-w_j)= k*diff^2 = k
                assert sum(x)==0 and dot(w,x)==k
                return x
    # fallback brute coefficients on two labels
    for vals in itertools.product(range(-10,11), repeat=D-1):
        x=list(vals)+[-sum(vals)]
        if dot(w,x)==k: return x
    raise AssertionError('no base')

ledger={'D':D,'source':str(SRC),'scope':'splice placement only for high-even D=9 anchor; reserve/terminal selector low-modulus RF2 not included','stages':[]}
log=[]
for stage in range(len(shifts)):
    E=active_graph_edges(stage)
    w, comps=primitive_band_function(E)
    # verify w const on active edges
    for e in E:
        assert dot(w,edgevec(e))==0
    st={'stage':stage+1,'height_shift':shifts[stage],'band_functional':w,'active_graph_edges':[edge_word(e) for e in E],'band_components':[comp for comp in comps],'parts':[]}
    bands=[]
    for pi,item in enumerate(supports[stage]['parts']):
        P=item['P']; M=[norm(e) for e in item['M']]; A=active_edges(stage,pi,item)
        band_value=pi
        b=solve_base_for_band(w,band_value)
        assert sum(b)==0 and dot(w,b)==band_value
        # active directions stay in band
        for e in A: assert dot(w,edgevec(e))==0
        part={'part_index':pi,'P':P,'support_edges':[edge_word(e) for e in M],'active_edges':[edge_word(e) for e in A],'band_value':band_value,'basepoint':b,'colors':[]}
        s=shifts[stage]; p=perms[stage]
        for c in P:
            tail=(c+s)%D; head=p[tail]; delta=norm((tail,head))
            color_entry={'color':c,'tail_slot':tail,'head_slot':head,'physical_increment':f'{tail}->{head}','previous_forest':[edge_word(e) for e in prev_edges(c,stage)]}
            # inactive and omitted coordinates of old head b+u_tail (we encode +u_tail by adding 1 if tail in labels)
            inactive=[]
            for f in M:
                labels=desc_labels(c,stage,M,f)
                # check active edge behavior in all support coords; for f inactive, active directions must vanish
                vals_on_active={edge_word(a):sum(edgevec(a)[i] for i in labels) for a in A}
                val=sum(b[i] for i in labels) + (1 if tail in labels else 0)
                entry={'edge':edge_word(f),'descendant_labels':labels,'old_head_value_at_base':val,'active_direction_values':vals_on_active}
                if f not in A:
                    assert all(v==0 for v in vals_on_active.values()), (stage+1,pi,c,f,vals_on_active)
                inactive.append(entry)
            om=omitted_labels(c,stage,M)
            om_active={edge_word(a):sum(edgevec(a)[i] for i in om) for a in A}
            assert all(v==0 for v in om_active.values())
            color_entry['omitted_labels']=om
            color_entry['omitted_value_at_base']=sum(b[i] for i in om)+(1 if tail in om else 0)
            color_entry['support_coordinates']=inactive
            # active coordinate values of physical increment delta in each active edge descendant coordinate
            color_entry['active_vector']=[sum(edgevec((tail,head))[i] for i in desc_labels(c,stage,M,a)) for a in A]
            part['colors'].append(color_entry)
        st['parts'].append(part)
        bands.append(band_value)
    assert len(set(bands))==len(bands)
    ledger['stages'].append(st)
    log.append(f'stage {stage+1}: active edges {",".join(edge_word(e) for e in E)}; band w={w}; part values={bands}')

OUT.write_text(json.dumps(ledger,indent=2))
TXT.write_text('OK: D9 affine splice-placement ledger verified\n'+'\n'.join(log)+'\n')
print(TXT.read_text())
print('wrote', OUT)
