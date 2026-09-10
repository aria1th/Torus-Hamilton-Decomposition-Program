#!/usr/bin/env python3
"""Schedule-independent D5(4) certificate checker, using only Python's library.

It checks actual positive physical basis arcs, not just abstract root returns.
The finite certificate is suitable for a later proof-assistant checker port;
this script itself is not a Lean kernel proof.
"""
from pathlib import Path
import json, argparse

ROOT=Path(__file__).resolve().parents[1]

def need(p,msg):
    if not p:raise ValueError(msg)

def vertex(i):
    h=i%4;k=i//4
    roots=[0]*4
    for j in range(3,-1,-1):roots[j]=k%4;k//=4
    return tuple(roots+[(h-sum(roots))%4])

def check(tours):
    need(len(tours)==5,'five tours required')
    used=[set() for _ in range(1024)]
    for c,tour in enumerate(tours):
        need(len(tour)==1024,'wrong tour length')
        need(set(tour)==set(range(1024)),'tour is not a permutation of all vertices')
        for k,s in enumerate(tour):
            x=vertex(s);y=vertex(tour[(k+1)%1024]);d=tuple((v-u)%4 for u,v in zip(x,y))
            need(sum(v!=0 for v in d)==1 and 1 in d,'not a positive coordinate arc')
            j=d.index(1);need(j not in used[s],'arc used by two colors');used[s].add(j)
    need(all(z==set(range(5)) for z in used),'arc partition incomplete')
    return {'vertices':1024,'colors':5,'hamilton_lengths':[1024]*5,'positive_colored_arcs':5120}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--out',default=str(ROOT/'TOUR_CERTIFICATE_REPORT.json'));a=ap.parse_args()
    cert=json.loads((ROOT/'certificates/d5_m4_tours.json').read_text());tours=cert['tours'];report=check(tours)
    tests={}
    variants={
      'short_tour':[t[:-1] if i==0 else t[:] for i,t in enumerate(tours)],
      'repeated_vertex':[t[:] for t in tours],
      'non_arc_permutation':[t[:] for t in tours],
      'duplicate_color':[t[:] for t in tours]}
    variants['repeated_vertex'][0][1]=variants['repeated_vertex'][0][0]
    variants['non_arc_permutation'][0][1],variants['non_arc_permutation'][0][2]=variants['non_arc_permutation'][0][2],variants['non_arc_permutation'][0][1]
    variants['duplicate_color'][1]=variants['duplicate_color'][0][:]
    for name,bad in variants.items():
        try:check(bad)
        except ValueError as e:tests[name]=str(e)
        else:raise ValueError('mutation was accepted: '+name)
    report.update({'all_passed':True,'schedule_imported':False,'formal_kernel_run':False,'rejected_mutations':tests})
    Path(a.out).write_text(json.dumps(report,indent=2));print(json.dumps(report,indent=2))
if __name__=='__main__':main()
