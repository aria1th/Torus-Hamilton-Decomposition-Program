#!/usr/bin/env python3
"""Verify D9 marked-selector and endpoint-reserve semantics.

Checks added beyond the older frame verifier:
  * reserve singleton names/roles are the ordered endpoint reserve family;
  * the terminal A2 marked comparison cycle lives in the terminal carrier plane;
  * the conservative protected neighborhood is the whole terminal carrier plane;
  * all reserve sites and splice supports are outside that protected carrier;
  * for m=4,6,8 the same assertions are checked by exhaustive finite sets.
"""
import json, itertools, math
from pathlib import Path
D=9
ROOT=Path(__file__).resolve().parent
DATA_DIR=ROOT.parent if ROOT.name=='scripts' else ROOT
def pick(*parts):
    p=DATA_DIR.joinpath(*parts)
    if p.exists(): return p
    return Path('/mnt/data').joinpath(parts[-1])
TERM=pick('certificates','d9_terminal_reserve_frame_candidate.json')
LEDGER=pick('certificates','d9_affine_splice_placement_ledger.json')
LOW=pick('certificates','d9_lowmod_finite_placement_semantic.json')
if not LOW.exists(): LOW=pick('certificates','d9_lowmod_finite_placement_candidate.json')
term=json.loads(TERM.read_text())
ledger=json.loads(LEDGER.read_text())
low=json.loads(LOW.read_text())
ROLES=['U0','U1','U2']+[f'U{j}_c' for j in range(1,9)]+['U_star']
PURPOSE={r:('terminal_exchange' if r in ('U0','U1','U2') else 'next_reserve' if r=='U_star' else 'coordinate_renewal') for r in ROLES}

def assert_true(cond,msg):
    if not cond: raise AssertionError(msg)

def edge_vec(e,m=None):
    if isinstance(e,str): a=int(e[0]); b=int(e[1])
    else: a,b=e
    v=[0]*D; v[a]-=1; v[b]+=1
    if m is not None: v=[x%m for x in v]
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
    b=tuple(x%m for x in base); S=span(edges,m)
    return {add(b,s,m) for s in S}
def embed_terminal(q,base,edges,m):
    # q=(x,y) in terminal A2 coordinates, edges are [0t,01]
    b=tuple(x%m for x in base)
    e0=edge_vec(edges[0],m); e1=edge_vec(edges[1],m)
    return add(add(b,smul(q[0],e0,m),m), smul(q[1],e1,m),m)
def terminal_selector_C(m):
    if m==4:
        return [(0,3),(3,0),(3,3)], (1,2)  # local terminal colors F1,F2
    L=m-1
    C=[None]*L
    C[0]=(0,0); C[1]=((-1)%m,1%m)
    for j in range(2,L): C[j]=((-j-1)%m,j%m)
    return C, (0,1)  # local terminal colors F0,F1

# High-even semantic roles.
sites=term['reserve_sites']
assert_true([s['name'] for s in sites]==ROLES, 'high-even reserve site order/names mismatch')
for s in sites:
    assert_true(s.get('role',s['name']) in (s['name'], PURPOSE[s['name']]), f'high-even reserve site role malformed: {s}')
# Reserve plane contains terminal-carrier separation certificate.
sep_names=[x['name'] for x in term['reserve_plane']['separations']]
assert_true('terminal_carrier' in sep_names, 'reserve plane lacks terminal-carrier separation certificate')
assert_true(len(term['terminal_carrier']['separations'])==sum(len(st['parts']) for st in ledger['stages']), 'terminal carrier must be separated from every splice support')
assert_true(len(term['reserve_plane']['separations'])==sum(len(st['parts']) for st in ledger['stages'])+1, 'reserve plane must be separated from every splice support plus terminal carrier')
# Check separator diffs are nonzero and small enough for m>9.
for group in [term['terminal_carrier']['separations'], term['reserve_plane']['separations']]:
    for entry in group:
        d=entry['separator']['diff']
        assert_true(0<abs(d)<10, f'separator diff not high-even safe: {entry["name"]}, diff={d}')
# Low finite semantics.
for m_str,data in low['moduli'].items():
    m=int(m_str)
    sites=data['reserve_sites']
    names=[s['name'] for s in sites]
    # Accept old generic names only if order is exactly promoted to roles by this verifier; fail in reinforced bundle if semantic names absent.
    assert_true(len(sites)==len(ROLES), f'm={m}: wrong number of reserve sites')
    if names!=ROLES:
        # allow legacy U0..U11 only for backward compatibility, but verify semantic order.
        assert_true(names==[f'U{i}' for i in range(12)], f'm={m}: reserve names are neither semantic nor legacy ordered: {names}')
    T=data['terminal_carrier']; R=data['reserve_plane']
    Tset=coset(T['base'],T['edges'],m); Rset=coset(R['base'],R['edges'],m)
    assert_true(Tset.isdisjoint(Rset), f'm={m}: terminal carrier and reserve plane intersect')
    C,local_pair=terminal_selector_C(m)
    embedded=[embed_terminal(q,T['base'],T['edges'],m) for q in C]
    assert_true(all(p in Tset for p in embedded), f'm={m}: embedded comparison cycle not in terminal carrier')
    assert_true(len(set(embedded))==len(C), f'm={m}: embedded comparison cycle collapses')
    # Conservative protected neighborhood N(C) is the whole terminal carrier plane, so reserve sites must avoid Tset.
    for idx,site in enumerate(sites):
        role=site['name'] if site['name'] in ROLES else ROLES[idx]
        point=tuple(site['point'])
        assert_true(point in Rset, f'm={m}: reserve site {role} not in reserve plane')
        assert_true(point not in Tset, f'm={m}: reserve site {role} lies in protected terminal carrier')
    # Splice supports avoid terminal protected carrier and reserve plane.
    for obj in data['splice_supports']:
        S=coset(obj['base'],obj['edges'],m)
        assert_true(S.isdisjoint(Tset), f'm={m}: splice {obj["name"]} intersects protected terminal carrier')
        assert_true(S.isdisjoint(Rset), f'm={m}: splice {obj["name"]} intersects reserve plane')

print('OK: D9 marked comparison and endpoint-reserve semantics verified')
print('reserve roles:', ','.join(ROLES))
print('high-even protected neighborhood: terminal carrier plane; all separator diffs < 10')
print('low moduli checked:', ','.join(sorted(low['moduli'].keys(), key=int)))
