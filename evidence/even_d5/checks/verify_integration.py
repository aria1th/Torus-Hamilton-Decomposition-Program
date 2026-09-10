#!/usr/bin/env python3
"""Exact, independent reconstruction of the degree-five integration bridge.

The schedule and terminal permutations are implemented directly below. No old
D5 constructor is imported. Matrix certificates are over Z (or mod 4 for the
single small-modulus case). Finite tests do not establish the universal theorem;
its chronological-transversal proof and symbolic endpoint words are in the TeX.
"""
from __future__ import annotations
import argparse, json, math
from pathlib import Path
from collections import defaultdict
from itertools import product
import numpy as np
from sympy import Matrix

ROOT=Path(__file__).resolve().parents[1]
A=((1,0),(0,1),(0,0))
EVENTS=((0,(0,2,1)),(0,(3,4)),(1,(1,0,4)),(1,(2,3)),(2,(2,4)))
RHO4=((0,1,2,3,4),(1,3,4,2,0),(4,2,3,0,1),(3,4,0,1,2))

def require(p: bool, message: str) -> None:
    if not bool(p): raise ValueError(message)

def omega(m:int,q:tuple[int,int])->tuple[int,int,int]:
    x,y=q
    rows={(1,0):(0,2,1),(3,0):(1,0,2),(1,1):(1,2,0),
          (2,1):(2,0,1),(0,2):(2,0,1),(2,2):(1,2,0),
          (0,3):(1,2,0),(1,3):(2,0,1)}
    if q in rows:return rows[q]
    if y==2 and 3<=x<m:return (2,1,0)
    if 4<=y<m and x==1:return (0,2,1)
    if 4<=y<m and x==m+3-y:return (1,0,2)
    return (0,1,2)

def endpoints(m:int):
    P=(0,2);Q=(0,3);C=(2,1)
    X=lambda t:(t,2)
    Y=lambda t:(1,t%m)
    Z=lambda t:(t,(3-t)%m)
    local_words=[
      [P]+[X(t) for t in range(m-1,1,-1)]+[Y(3),Q]+[Z(t) for t in range(m-1,2,-1)]+[C,Y(1)],
      [P,Y(1),Y(0)]+[Y(t) for t in range(m-1,2,-1)]+[X(2),C]+[Z(t) for t in range(3,m)]+[Q],
      [P,Q]+[Y(t) for t in range(3,m)]+[Y(0),Y(1),C]+[X(t) for t in range(2,m)]
    ]
    flat=lambda pairs:[x for pair in pairs for x in pair]
    terminal_words=[
      [P]+flat((Z(t),X(t-1)) for t in range(m-1,2,-2))+[Y(1),Q]
      +flat((X(t),Z(t-1)) for t in range(m-1,4,-2))+[X(3),C,Y(3)],
      [P,C,Y(0)]+flat((Z(t),Y(m+2-t)) for t in range(4,m-1,2))
      +[Q,X(2),Y(1),Z(3)]+flat((Y(m+4-t),Z(t)) for t in range(5,m,2))+[Y(3)],
      [P,C]+flat((Y(t),X(t)) for t in range(3,m,2))+[Y(1),Q,X(2)]
      +flat((Y(t),X(t)) for t in range(4,m-1,2))+[Y(0)]
    ]
    result=[]
    candidates=set([P,Q,C,(1,0),(1,1),(1,3),(2,2),(3,0)]
                   +[(t,2) for t in range(3,m)]
                   +[(1,t) for t in range(4,m)]
                   +[(m+3-t,t) for t in range(4,m)])
    for i in range(3):
        B=sorted(q for q in candidates if omega(m,q)[i]!=i)
        require(len(B)==2*m,'endpoint support size')
        j={q:tuple((q[k]-A[i][k]+A[omega(m,q)[i]][k])%m for k in (0,1)) for q in B}
        require(set(j.values())==set(B),'local plane map not bijective')
        fibers=defaultdict(list)
        for q in B:
            f=q[0] if i==0 else q[1] if i==1 else sum(q)
            fibers[f%m].append(q)
        require(len(fibers)==m and all(len(v)==2 for v in fibers.values()),'two points per quotient fiber')
        N={p:v[1-k] for v in fibers.values() for k,p in enumerate(v)}
        for word,perm in ((local_words[i],j),(terminal_words[i],{q:N[j[q]] for q in B})):
            require(len(word)==2*m and len(set(word))==2*m and set(word)==set(B),'symbolic word coverage')
            require(all(perm[x]==word[(k+1)%len(word)] for k,x in enumerate(word)), 'symbolic successor identity')
        result.append((B,j,N,terminal_words[i]))
    return result

def lattice_data(small:bool=False):
    e=[Matrix.eye(4)[:,i] for i in range(4)]+[Matrix.zeros(4,1)]
    alpha=lambda a,b:e[b]-e[a]
    W=[[alpha(0,1),alpha(0,2),alpha(0,3)],
       [alpha(0,1),alpha(0,3),alpha(3,4)],
       [alpha(0,1),alpha(0,4)], [alpha(0,2),alpha(2,3)], [alpha(2,4)]]
    neutral=lambda c,t:RHO4[t][c] if small else (c+t)%5
    H=[[sum((e[neutral(c,t)] for t in range(4)),Matrix.zeros(4,1))]
       if small else [sum(e[:4],Matrix.zeros(4,1))-5*e[c]] for c in range(5)]
    rows=[]
    for p,(t,word) in enumerate(EVENTS):
        for c in range(5):
            dr=neutral(c,t)
            if dr not in word:continue
            newdr=word[(word.index(dr)+1)%len(word)];v=alpha(dr,newdr)
            Q=Matrix.hstack(*(H[c]+W[p]));det=int(Q.det());r=len(H[c])
            require(det%2!=0 if small else abs(det)==1,'complement determinant')
            inv=Q.inv_mod(4) if small else Q.inv()
            coeff=inv*v; wc=[int(coeff[k])%4 if small else int(coeff[k]) for k in range(r,4)]
            require(all((int(coeff[k])%4==0 if small else coeff[k]==0) for k in range(r)), 'edge outside W')
            require(math.gcd(4,*wc)==1 if small else math.gcd(*wc)==1,'primitive W-coordinate')
            row={'component':p,'color':c,'rank_before':r,'neutral_direction':dr,
                 'changed_direction':newdr,'edge':[int(z) for z in v],
                 'H_before':[[int(z) for z in col] for col in H[c]],
                 'matrix':[[int(z) for z in line] for line in Q.tolist()],
                 'determinant':det,'W_coordinates':wc}
            rows.append(row);H[c].append(v)
    require(len(rows)==12,'twelve gates expected')
    chars={2:(1,0,0,-1),3:(1,-1,0,0),4:(0,-1,1,0)} if small else {
        1:(2,2,3,3),3:(-1,0,1,0),4:(0,-1,1,0)}
    for c,f in chars.items():
        mat=Matrix.hstack(*H[c]);require(Matrix([f])*mat==Matrix.zeros(1,3),'annihilator equality over Z')
    return rows,H,chars

def cycles(p:np.ndarray):
    require(np.array_equal(np.sort(p),np.arange(len(p))),'not a permutation')
    ids=np.full(len(p),-1,dtype=np.int64);lengths=[]
    for s in range(len(p)):
        if ids[s]>=0:continue
        v=s;l=0;k=len(lengths)
        while ids[v]<0:ids[v]=k;v=int(p[v]);l+=1
        require(v==s,'orbit does not close');lengths.append(l)
    return ids,lengths

def masks(X,m):
    x0,x1,x2,x3=X.T;s=(x0+x1+x2+x3)%m
    return (s==0,x2==1,(x2==0)&(x3==0),(x1==0)&(s==m-1),
            (x0==0)&(x1==0)&(x3==0))

def schedule(m,X,t,terminal=False):
    rho=RHO4[t] if m==4 else tuple((c+t)%5 if t<5 else c for c in range(5))
    D=np.tile(rho,(len(X),1)); ms=masks(X,m)
    for p,(tt,word) in enumerate(EVENTS):
        if tt!=t:continue
        before=D[ms[p]].copy()
        after=before.copy()
        for k,dr in enumerate(word):after[before==dr]=word[(k+1)%len(word)]
        D[ms[p]]=after
    if terminal and t==2:
        plane=(X[:,2]==0)&((X[:,0]+X[:,1]+X[:,3])%m==0)
        for k in np.flatnonzero(plane):
            w=omega(m,(int(X[k,3]),int(X[k,0])));old=D[k].copy();dirs=(3,0,1)
            for i,dr in enumerate(dirs):D[k,old==dr]=dirs[w[i]]
    require(np.all(np.sort(D,axis=1)==np.arange(5)),'source Latin condition')
    return D

def add_vector(X,v,m,powers):return ((X+np.array(v,dtype=np.int64))%m)@powers

def layer(X,D,c,m,powers):
    Y=X.copy();rows=np.flatnonzero(D[:,c]<4);col=D[rows,c]
    Y[rows,col]=(Y[rows,col]+1)%m
    return Y@powers

def compose(layers,start=0):
    r=np.arange(len(layers[0]));m=len(layers)
    for k in range(m):r=layers[(start+k)%m][r]
    return r

def finite_bridge(m:int):
    X=np.array(list(product(range(m),repeat=4)),dtype=np.int64)
    n=len(X);pw=np.array([m**3,m**2,m,1],dtype=np.int64);ID=np.arange(n)
    rows,finalH,chars=lattice_data(m==4);ms=masks(X,m)
    trace=[];pre_layers=[]
    for c in range(5):
        layers=[add_vector(X,[int(j== (RHO4[t][c] if m==4 else (c+t)%5 if t<5 else c)) for j in range(4)],m,pw) for t in range(m)]
        for rec in (r for r in rows if r['color']==c):
            p=rec['component'];t=EVENTS[p][0];r=rec['rank_before']
            before=compose(layers);cid,L=cycles(before)
            require(all(l==m**r for l in L),'old cycle lengths')
            Q=Matrix(rec['matrix']);Qi=np.array(Q.inv_mod(m)).astype(np.int64)
            keys=(X@Qi.T)%m
            # Quotient coordinates are the W coordinates in H (+) W.
            quotient=keys[:,r:]@np.array([m**j for j in reversed(range(4-r))])
            qid=np.unique(quotient,return_inverse=True)[1]
            require(len(set(qid))==len(L),'old quotient count')
            representatives=np.full(len(L),-1,dtype=np.int64)
            for j in range(n):
                if representatives[cid[j]]<0:representatives[cid[j]]=qid[j]
                require(representatives[cid[j]]==qid[j],'old orbit is not its H coset')
            pref=ID.copy()
            for u in range(t):pref=layers[u][pref]
            invpref=np.empty(n,dtype=np.int64);invpref[pref]=ID
            support=np.flatnonzero(ms[p][pref])
            require(np.all(np.bincount(qid[support],minlength=len(L))==1),'pulled-back support is not an exact transversal')
            displacements=(X[pref]-X)%m
            qdis=(displacements@Qi.T)%m
            require(np.all(qdis[:,r:]==qdis[0,r:]),'prefix quotient translation failure')
            J=ID.copy();J[ms[p]]=add_vector(X[ms[p]],rec['edge'],m,pw)
            q=invpref[J[pref]]
            layers[t]=layers[t][J]
            after=compose(layers)
            require(np.array_equal(after,before[q]),'chronological right-composition identity')
            _,NL=cycles(after)
            require(len(NL)==m**(3-r) and all(l==m**(r+1) for l in NL),'rank-one splice failure')
            # Each nontrivial comparison component meets m distinct old cycles.
            used=set()
            for s in support:
                if int(s) in used:continue
                v=int(s);orbit=[]
                while v not in used:used.add(v);orbit.append(v);v=int(q[v])
                require(v==s and len(orbit)==m and len(set(cid[orbit]))==m,'comparison not a transversal m-cycle')
            trace.append({'color':c,'component':p,'rank_before':r,'old_cycles':len(L),'new_cycles':len(NL),
                          'pulledback_source_count':len(support),'prefix_translation':True,'comparison_identity':True})
        printed=[layer(X,schedule(m,X,t,False),c,m,pw) for t in range(m)]
        require(all(np.array_equal(a,b) for a,b in zip(layers,printed)),'stage construction differs from printed schedule')
        pre_layers.append(layers)
    enddata=endpoints(m);endchecks=[]
    for i,c in enumerate((2,3,4) if m==4 else (1,3,4)):
        before=compose(pre_layers[c],2);cid,L=cycles(before)
        B,j,N_formula,word=enddata[i]
        phi=lambda q:np.array([q[1],(-sum(q))%m,0,q[0]],dtype=np.int64)
        points=[int(phi(q)@pw) for q in B];lookup=dict(zip(points,B))
        allhit=np.bincount(cid[points],minlength=len(L))
        require(np.all(allhit>0),'unhit preterminal cycle')
        if m>=6:require(np.all(allhit==2),'not two cuts per old cycle')
        N={};times={}
        for s,q0 in zip(points,B):
            v=int(before[s]);k=1
            while v not in lookup:
                v=int(before[v]);k+=1;require(k<=n,'nontermination')
            N[q0]=lookup[v];times[str(q0)]=k
        if m>=6:require(N==N_formula,'actual first return differs from quotient fibre swap')
        else:
            expected=[
              [[(0,2),(1,3)],[(0,3),(2,1),(3,2)],[(1,1),(2,2)],[(3,0)]],
              [[(0,2),(2,1)],[(0,3),(2,2)],[(1,1),(1,3),(3,0)],[(1,0)]],
              [[(0,2),(1,1)],[(0,3),(2,1)],[(1,0),(3,2)],[(1,3),(2,2)]]][i]
            N_expected={q:w[(j+1)%len(w)] for w in expected for j,q in enumerate(w)}
            require(N==N_expected,'modulus-four printed first-return table')
            tests={2:[((0,3),38,(2,1)),((0,3),59,(3,2))],
                   3:[((1,1),30,(1,3)),((1,1),47,(3,0))],4:[]}[c]
            for q0,k,q1 in tests:
                v=int(phi(q0)@pw)
                for _ in range(k):v=int(before[v])
                require(v==int(phi(q1)@pw),'printed modulus-four iterate identity')
        post_layers=[layer(X,schedule(m,X,t,True),c,m,pw) for t in range(m)]
        after=compose(post_layers,2)
        Jplane=ID.copy()
        for q0,s in zip(B,points):Jplane[s]=int(phi(j[q0])@pw)
        require(np.array_equal(after,before[Jplane]),'terminal insertion is not R J in physical section')
        productmap={q:N[j[q]] for q in B};seq=[];q0=min(B)
        while q0 not in seq:seq.append(q0);q0=productmap[q0]
        require(len(seq)==len(B) and q0==seq[0],'terminal endpoint circuit failure')
        _,LP=cycles(after);require(LP==[n],'root-return not Hamilton')
        endchecks.append({'color':c,'endpoint_count':len(B),'cuts_per_old_cycle':allhit.tolist(),
                          'return_times':times,'N_cycles':cycle_word_map(N),'product_cycle':seq})
    physical=[];tours=[]
    for c in range(5):
        S=np.empty(n*m,dtype=np.int64)
        for t in range(m):
            D=schedule(m,X,t,True);out=layer(X,D,c,m,pw)
            cycles(out)
            S[ID*m+t]=out*m+(t+1)%m
        _,lengths=cycles(S);require(lengths==[m**5],'full physical Hamilton failure')
        physical.append(lengths)
        if m==4:
            v=0;tour=[]
            for _ in range(len(S)):tour.append(v);v=int(S[v])
            require(v==0,'tour closure');tours.append(tour)
    if m==4:
        (ROOT/'certificates').mkdir(exist_ok=True)
        (ROOT/'certificates'/'d5_m4_tours.json').write_text(json.dumps({
          'coordinates':'x0,x1,x2,x3,h; vertex id=4*base4(x0,x1,x2,x3)+h; physical fifth coordinate=h-sum(x)',
          'tours':tours},separators=(',',':')))
    return {'m':m,'root_vertices':n,'physical_vertices':n*m,'stage_checks':trace,
            'endpoint_checks':endchecks,'physical_terminal_lengths':physical,
            'full_terminal_colored_arc_observations':5*m**5}

def cycle_word_map(p):
    unseen=set(p);out=[]
    while unseen:
        x=min(unseen);s=x;w=[]
        while x in unseen:unseen.remove(x);w.append(x);x=p[x]
        require(x==s,'not permutation');out.append(w)
    return out

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--out',default=str(ROOT/'INTEGRATION_REPORT.json'))
    ap.add_argument('--moduli',nargs='+',type=int,default=[4,6,8,10,12]);ap.add_argument('--endpoint-max',type=int,default=256)
    args=ap.parse_args();report={'scope':'New chronological-transversal and endpoint audit; not a Lean proof.',
       'formal_kernel_run':False,'universal_conclusions_from_finite_tests':False,'all_passed':False}
    target=Path(args.out)
    try:
        require(all(m>=4 and m%2==0 for m in args.moduli),'bad modulus')
        report['integer_certificates']=lattice_data(False)[0]
        report['mod4_certificates']=lattice_data(True)[0]
        report['symbolic_endpoint_moduli']=list(range(4,args.endpoint_max+1,2))
        for m in report['symbolic_endpoint_moduli']:endpoints(m)
        report['finite_cases']=[]
        for m in args.moduli:
            report['finite_cases'].append(finite_bridge(m));target.write_text(json.dumps(report,indent=2))
        report['all_passed']=True
    except Exception as e:
        report['error']=repr(e);target.write_text(json.dumps(report,indent=2));raise
    target.write_text(json.dumps(report,indent=2))
    print(json.dumps({'all_passed':report['all_passed'],'finite_moduli':args.moduli,
          'endpoint_moduli':len(report['symbolic_endpoint_moduli']),
          'stage_checks':sum(len(x['stage_checks']) for x in report['finite_cases']),
          'physical_terminal_arc_observations':sum(x['full_terminal_colored_arc_observations'] for x in report['finite_cases'])},indent=2))
if __name__=='__main__':main()
