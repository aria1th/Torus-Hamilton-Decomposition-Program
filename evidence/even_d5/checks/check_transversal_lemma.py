#!/usr/bin/env python3
"""Finite counterchecks for the abstract chronological-transversal lemma.
No schedule or torus constructor is used. Randomness has a fixed seed.
"""
import random,json,argparse
from pathlib import Path
from itertools import product
ROOT=Path(__file__).resolve().parents[1]

def check(S):
    if set(S)!=set(S.values()):raise ValueError('not bijective')
    unseen=set(S);orbits=[]
    while unseen:
        x=min(unseen);s=x;o=[]
        while x in unseen:unseen.remove(x);o.append(x);x=S[x]
        if x!=s:raise ValueError('not a closed orbit')
        orbits.append(o)
    return orbits

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--out',default=str(ROOT/'TRANSVERSAL_LEMMA_REPORT.json'));a=ap.parse_args()
    rng=random.Random(571903);count=0;raw_diff=0;nonquotient_fail=None
    for m in (3,4,5,6,8):
      V=list(product(range(m),repeat=3))
      for rep in range(20):
        S={};P={};dy=rng.randrange(m);dz=rng.randrange(m)
        for y,z in product(range(m),repeat=2):
            word=list(range(m));rng.shuffle(word)
            sigma=list(range(m));rng.shuffle(sigma)
            for k,x in enumerate(word):S[x,y,z]=(word[(k+1)%m],y,z)
            for x in range(m):P[x,y,z]=(sigma[x],(y+dy)%m,(z+dz)%m)
        Pi={v:k for k,v in P.items()};h=rng.randrange(m)
        J={v:((v[0],(v[1]+1)%m,(v[2]+2)%m) if v[0]==h else v) for v in V}
        r={v:Pi[J[P[v]]] for v in V};out={v:S[r[v]] for v in V}
        O=check(out)
        if len(O)!=m or any(len(o)!=m*m for o in O):raise ValueError('wrong orbit count/length')
        if any(len({(z-2*y)%m for x,y,z in o})!=1 for o in O):raise ValueError('wrong new cosets')
        if out!={v:S[J[v]] for v in V}:raw_diff+=1
        count+=1
        if nonquotient_fail is None:
            for attempt in range(8):
                bad=P.copy();x,y=rng.sample(V,2);bad[x],bad[y]=bad[y],bad[x]
                inv={v:k for k,v in bad.items()};badout={v:S[inv[J[bad[v]]]] for v in V};badO=check(badout)
                if len(badO)!=m or any(len(o)!=m*m or len({(z-2*y)%m for x,y,z in o})!=1 for o in badO):
                    nonquotient_fail={'m':m,'swapped_prefix_sources':[x,y],
                        'cycle_lengths':[len(o) for o in badO],
                        'correct_conclusion_failed':True};break
    if nonquotient_fail is None:raise ValueError('missing negative control')
    R={'all_passed':True,'instances':count,'raw_J_is_not_pulledback_J_instances':raw_diff,
       'prefix_quotient_negative_control':nonquotient_fail,'random_seed':571903,
       'scope':'Abstract finite abelian permutation test; not additional physical torus cases.'}
    Path(a.out).write_text(json.dumps(R,indent=2));print(json.dumps(R,indent=2))
if __name__=='__main__':main()
