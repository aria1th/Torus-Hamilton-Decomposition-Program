"""Independent small-entry replay for the collar induction.

No previous constructor is imported. Parameters checked are explicit finite
instances; generality rests on the symbolic entry and collar lemmas.
"""
from __future__ import annotations
import json
from pathlib import Path
from collections import defaultdict, deque
from itertools import product
from math import gcd
import numpy as np
try:
    from numba import njit
except ImportError:
    def njit(f): return f


def need(ok, message):
    if not bool(ok): raise ValueError(message)


def core(M, v):
    x,y,w=v; h=(x+y+w)%M
    if h==0: return (2,1,0)
    if h==1: return (0,2,1) if w in (0,1) else (1,2,0)
    if h==2 and w==0: return (1,0,2)
    return (0,1,2)


def terminal(M,v):
    x,y,w=v; h=(x+y+w)%M
    if h==1:
        a=y%M; b=(w-3)%M
        if a==0 and b==0: row=(0,1,2)
        else:
            if (a+b)%M==0: z,t=0,a
            elif a==0: z,t=1,b
            elif b==0: z,t=2,(-a)%M
            else: z,t=None,None
            if z is None: row=(0,1,2)
            elif t==1: row=(2,0,1)
            elif t==M-1: row=(1,2,0)
            else: row=tuple((2*z-c)%3 for c in range(3))
    else:
        power=1 if h==2 else (2 if M%3 or h in (0,3,4) else 0)
        row=tuple((c+power)%3 for c in range(3))
    return tuple(row[c] for c in (0,2,1))


def shell(M,p,h,w):
    need(p in (2,3),'only the two new low-entry specializations are supported')
    W=({p}|set(range(1,p))) if h==0 else ({0}|set(range(p+1,2*p))) if h==1 else set(range(p))
    eligible=set(range(2*p))-W
    if p==2:
        pairs=[(0,3)] if h==0 else [(2,1)] if h==1 else []
    else:
        pairs=[(0,4)] if h==0 else [(1,2)] if h==1 else [(3,5)] if h==2 else []
    used=set(v for pair in pairs for v in pair)
    sel=set(sorted(eligible-used)[:1-len(pairs)])
    for a,b in pairs: sel.add(b if w==0 else a)
    return tuple(2 if c in W else 1 if c in sel else 0 for c in range(2*p))


def initial_selection(M,p,v):
    x,y,w=v; h=sum(v)%M
    anchors=[(0,1,0),(1,1,0),(0,0,0),(0,M-2,3)]
    locations=[(1,0),(2,0),(0,0),(1,3)]
    mates=[2,3,0,1] if p==2 else [1,3,0,2] # shell indexing A_i=i, B_i=p+i
    if (h,w) in locations:
        k=locations.index((h,w))
        return (k if k<2 else 2,) if tuple(v)==anchors[k] else (3+mates[k],)
    eligible=[3+c for c,a in enumerate(shell(M,p,h,w)) if a==0]
    if p==3 and (h,w)==(0,1):
        return (3+5 if x==0 else 3+4,)
    return (eligible[0],)


def label(c,l): return c if c<2 else 2+l if c==2 else c+1

def color(l): return l if l<2 else 2 if l<4 else l-1


def components(supports, q):
    par=list(range(q))
    def root(a):
        while par[a]!=a: par[a]=par[par[a]];a=par[a]
        return a
    for S in supports:
        for a in S[1:]:par[root(a)]=root(S[0])
    groups=defaultdict(list)
    for a in range(q):groups[root(a)].append(a)
    return sorted(sorted(v) for v in groups.values())


def tjoin(supports,q):
    # Node 0..q-1: all orbit columns, including isolated ones.
    adj=[[] for _ in range(q+len(supports))]
    for j,S in enumerate(supports):
        for a in S:adj[a].append(q+j);adj[q+j].append(a)
    seen=set(); selected=[[] for _ in supports]
    for root in range(q):
        if root in seen:continue
        order=[root];parent={root:None};seen.add(root)
        for u in order:
            for v in adj[u]:
                if v not in seen:seen.add(v);parent[v]=u;order.append(v)
        parity={v:int(v<q) for v in order}
        for v in reversed(order[1:]):
            if parity[v]:
                u=parent[v];parity[u]^=1
                a,j=(v,u-q) if v<q else (u,v-q)
                selected[j].append(a)
        need(parity[root]==0,'odd incidence component')
    edges=[]
    for j,S in enumerate(selected):
        S.sort();need(len(S)%2==0,'odd degree at block')
        edges.extend((S[k],S[k+1],j) for k in range(0,len(S),2))
    # Euler orientation after adjoining one dummy edge at every odd column.
    deg=[0]*q
    for a,b,j in edges:deg[a]+=1;deg[b]+=1
    need(all(n%2==1 for n in deg),'orbit degree is not odd')
    all_edges=[(a,b) for a,b,j in edges]+[(q,a) for a in range(q)]
    a2=[[] for _ in range(q+1)]
    for k,(a,b) in enumerate(all_edges):a2[a].append((b,k));a2[b].append((a,k))
    used=set(); oriented=[None]*len(all_edges)
    for root in range(q+1):
        stack=[root]
        while stack:
            a=stack[-1]
            while a2[a] and a2[a][-1][1] in used:a2[a].pop()
            if not a2[a]:stack.pop();continue
            b,k=a2[a].pop();used.add(k);oriented[k]=(a,b);stack.append(b)
    local=defaultdict(list);div=[0]*q
    for k,(_,_,j) in enumerate(edges):
        a,b=oriented[k];local[j].append((a,b));div[a]+=1;div[b]-=1
    need(all(abs(x)==1 for x in div),'Euler divergence')
    return local


def connected(rows):
    reached={0}
    while True:
        old=len(reached)
        for j,S in enumerate(rows):
            if j not in reached and any(set(S)&set(rows[k]) for k in reached):reached.add(j)
        if len(reached)==old:return len(reached)==len(rows)


def pinned(M,S,pairs):
    b=len(S)//2;active=set(S)&set(range(4));need(len(active)<=1,'active collision')
    pairs=list(pairs)
    k=next((j for j,e in enumerate(pairs) if set(e)&active),None)
    if k is not None:pairs[0],pairs[k]=pairs[k],pairs[0]
    phase=0 if k is None or pairs[0][0] in active else 1
    used=set(v for e in pairs for v in e)
    need(len(used)==2*len(pairs),'non-disjoint pairs')
    fill=set(sorted(set(S)-used-active)[:b-len(pairs)])
    need(len(fill)==b-len(pairs),'insufficient inactive fillers')
    rows=[]
    for t in range(M):
        R=fill|{v if t==(1-phase if j==1 else phase) else u for j,(u,v) in enumerate(pairs)}
        need(len(R)==b,'wrong local quota');rows.append(sorted(R))
    need(not active.intersection(rows[0]),'row-zero violation')
    if b>=2:need(connected(rows),'selected coherence')
    if len(S)-b>=2:need(connected([sorted(set(S)-set(R)) for R in rows]),'complement coherence')
    return rows


def seed(M,p):
    vs=np.array(list(product(range(M),repeat=3)),dtype=np.int64)
    ds=np.array([core(M,tuple(v))+shell(M,p,int(sum(v)%M),int(v[2])) for v in vs],dtype=np.int16)
    labs=np.array([(int(v[2])-max(int(sum(v)%M)-2,0))%2 for v in vs],dtype=np.int8)
    return vs,ds,labs,[p-p//2+1,p//2+1,p+1]


def physical_lift(M,vs,ds,labs,parts,i,chosen):
    N,d=ds.shape;a=parts[i];b=a//2
    need(np.all(chosen.sum(axis=1)==b),'row quota')
    need(not np.any(chosen & (ds!=i)),'selected ineligible color')
    totals=[]
    for c in range(d):
        if c==2:totals.extend(int(chosen[labs==l,c].sum()) for l in (0,1))
        else:totals.append(int(chosen[:,c].sum()))
    need(all(gcd(n,M)==1 for n in totals),'nonunit carry')
    nd=ds.copy();nd[ds>i]+=1;nd[chosen]=i+1;nd=np.repeat(nd,M,axis=0)
    nv=np.repeat(vs,M,axis=0);ts=np.tile(np.arange(M),N)
    nv=np.column_stack([nv[:,:i],(nv[:,i]-ts)%M,ts,nv[:,i+1:]])
    nl=np.repeat(labs,M)
    nparts=parts[:i]+[a-b,b]+parts[i+1:]
    # All new fibre blocks have constant full profiles and orbit labels.
    for j,w in enumerate(nparts):
        if w<2:continue
        profiles=np.unique(np.column_stack([nd[::M],nl[::M]]),axis=0)
        supports=[tuple(label(c,int(v[-1])) for c,k in enumerate(v[:-1]) if k==j) for v in profiles]
        G=components(supports,d+1)
        need(all(len(C)%2==0 for C in G),'new odd component')
    return nv,nd,nl,nparts,totals


@njit
def cycles(succ):
    N=succ.shape[0];seen=np.zeros(N,np.uint8);lens=[]
    for s in range(N):
        if seen[s]:continue
        x=s;n=0
        while not seen[x]:seen[x]=1;n+=1;x=succ[x]
        if x!=s:raise ValueError('not a union of permutation cycles')
        lens.append(n)
    return sorted(lens)


def audit(M,vs,ds,parts):
    N,d=ds.shape;n=len(parts)
    for i,a in enumerate(parts):need(np.all((ds==i).sum(axis=1)==a),'direction multiplicity')
    powers=np.array([M**j for j in reversed(range(n))],dtype=np.int64)
    ids=vs@powers
    need(len(np.unique(ids))==N and int(ids.min())==0 and int(ids.max())==N-1,'coordinate bijection')
    inv=np.empty(N,dtype=np.int64);inv[ids]=np.arange(N)
    result=[]
    for c in range(d):
        a=ds[:,c].astype(np.int64);coordinate=vs[np.arange(N),a]
        head=ids+np.where(coordinate==M-1,1-M,1)*powers[a]
        succ=inv[head]
        need(np.all(np.bincount(succ,minlength=N)==1),'indegree')
        result.append(cycles(succ))
    return result


def patch(M,p,ds,n):
    out=ds.copy();factor=M**(n-3)
    for k,v in enumerate(product(range(M),repeat=3)):
        old=core(M,v);new=terminal(M,v)
        if old!=new:
            idx=k*factor;before=out[idx,:3].copy()
            out[idx,:3]=[before[old.index(new[c])] for c in range(3)]
    need(np.array_equal(out[:,3:],ds[:,3:]),'passive changed')
    return out


def run(M,p,full=True):
    vs,ds,labs,parts=seed(M,p);d=2*p+3
    qrows=[(0,1,0),(1,1,0),(0,0,0),(0,M-2,3)]
    need(all(core(M,v)==terminal(M,v) for v in qrows),'anchor incompatibility')
    checked=[]
    def check():
        nr=audit(M,vs,ds,parts);tr=audit(M,vs,patch(M,p,ds,len(parts)),parts)
        need([len(x) for x in nr]==[1,1,2]+[1]*(d-3),'near inventory')
        need(all(x==[len(vs)] for x in tr),'terminal inventory')
        checked.append({'coordinates':len(parts),'vertices':len(vs),'near_lengths':nr,'terminal_lengths':tr})
    check()
    chosen=np.zeros_like(ds,dtype=np.bool_)
    for k,v in enumerate(vs):chosen[k,list(initial_selection(M,p,tuple(v)))]=True
    vs,ds,labs,parts,tot=physical_lift(M,vs,ds,labs,parts,0,chosen)
    need(tot[:4]==[1]*4,'entry active carries')
    first_totals=tot;check()
    ledger=[]
    if full:
        while max(parts)>1:
            i=max(range(len(parts)),key=lambda j:(parts[j],-j))
            b=parts[i]//2
            # Profile of old block; only one representative block per type is exceptional.
            keys,first,inverse=np.unique(np.column_stack([ds[::M],labs[::M]]),axis=0,return_index=True,return_inverse=True)
            supports=[tuple(label(c,int(v[-1])) for c,k in enumerate(v[:-1]) if k==i) for v in keys]
            local=tjoin(supports,d+1)
            base=np.zeros((len(keys),d),dtype=np.bool_)
            for j,S in enumerate(supports):
                cols=[color(l) for l in sorted(S) if l>=4][:b]
                need(len(cols)==b,'passive baseline quota');base[j,cols]=True
            chosen=np.repeat(base[inverse],M,axis=0)
            for j,S in enumerate(supports):
                rows=pinned(M,S,local[j]);k=int(first[j])*M;chosen[k:k+M]=False
                for t,R in enumerate(rows):chosen[k+t,[color(l) for l in R]]=True
            need(not np.any(chosen[::M,:3]),'collar pin')
            oldparts=parts.copy()
            vs,ds,labs,parts,tot=physical_lift(M,vs,ds,labs,parts,i,chosen)
            ledger.append({'old_parts':oldparts,'split':i,'orbit_totals':tot})
        check()
    return {'M':M,'d':d,'full_simple_endpoint':bool(full),'entry_mates':(['B0','B1','A0','A1'] if p==2 else ['A1','B0','A0','A2']),
            'first_orbit_totals':first_totals,'states':checked,'later_splits':ledger,
            'colored_arc_observations':sum(2*d*s['vertices'] for s in checked)}


if __name__=='__main__':
    report={'scope':'Independent explicit d=7 and d=9 entry plus full collar replay at listed finite parameters. No Lean execution.',
            'cases':[],'all_passed':False}
    target=Path(__file__).with_name('SMALL_ENTRY_REPORT.json')
    try:
        for M,p,full in [(4,2,True),(6,2,True),(4,3,True),(6,3,False),(8,2,False),(8,3,False)]:
            report['cases'].append(run(M,p,full))
            target.write_text(json.dumps(report,indent=2))
        report['all_passed']=True
    except Exception as e:
        report['error']=repr(e)
        target.write_text(json.dumps(report,indent=2));raise
    target.write_text(json.dumps(report,indent=2))
    print(json.dumps({'all_passed':report['all_passed'],'parameters':[(c['M'],c['d'],c['full_simple_endpoint']) for c in report['cases']],
                      'colored_arc_observations':sum(c['colored_arc_observations'] for c in report['cases'])},indent=2))
