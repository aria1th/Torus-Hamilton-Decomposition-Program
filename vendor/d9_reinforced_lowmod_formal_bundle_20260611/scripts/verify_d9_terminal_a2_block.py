#!/usr/bin/env python3
"""Verify the D9 terminal A2 carrier semantics.

This verifier deliberately checks more than geometric separation.  It checks
that the terminal carrier recorded in the D9 certificates is exactly the
standard terminal A2 block transported to the shifted triple (6,0,1), and it
independently recomputes the terminal return maps on a range of even moduli.
The all-even statement still rests on the terminal-A2 theorem; the finite
recomputations are a guard against convention/transport errors in the D9 data.
"""
import json, math, itertools, sys
from pathlib import Path
D=9
ROOT=Path(__file__).resolve().parent
# tolerate execution from bundle/scripts or /mnt/data
DATA_DIR=ROOT.parent if (ROOT.name=='scripts') else ROOT
ACTIVE=DATA_DIR/'certificates'/'d9_active_anchor_candidate_v1.json'
TERM=DATA_DIR/'certificates'/'d9_terminal_reserve_frame_candidate.json'
if not ACTIVE.exists(): ACTIVE=Path('/mnt/data/d9_active_anchor_candidate_v1.json')
if not TERM.exists(): TERM=Path('/mnt/data/d9_terminal_reserve_frame_candidate.json')
active=json.loads(ACTIVE.read_text())
term=json.loads(TERM.read_text())

def assert_true(cond,msg):
    if not cond:
        raise AssertionError(msg)

def det(a,b): return a[0]*b[1]-a[1]*b[0]

def edge_vec_word(e):
    i=int(e[0]); j=int(e[1])
    v=[0]*D; v[i]-=1; v[j]+=1
    return v

def add2(a,b,m): return ((a[0]+b[0])%m,(a[1]+b[1])%m)
def sub2(a,b,m): return ((a[0]-b[0])%m,(a[1]-b[1])%m)
def smul2(k,a,m): return ((k*a[0])%m,(k*a[1])%m)

# 1. Transport/alignment checks against the active anchor.
rows=active['rows_shifted']; shifts=active['shifts']
assert_true(rows[-1]['triple']==[6,0,1], f"terminal shifted triple is {rows[-1]['triple']}, not [6,0,1]")
assert_true(shifts[-1]==7, f"terminal height shift is {shifts[-1]}, not 7")
al=term['terminal_alignment']
assert_true(al['root_vertices']==[6,0,1], 'terminal root_vertices mismatch')
assert_true(al['height_shift']==7, 'terminal height_shift mismatch')
chron=[(x-al['height_shift'])%D for x in al['root_vertices']]
assert_true(chron==al['terminal_triple_chronological'], f"chronological triple mismatch: {chron} vs {al['terminal_triple_chronological']}")
t=al['root_vertices'][0]
assert_true(al['root_vertices'][1:]==[0,1] and t not in (0,1), 'root vertices not of form (t,0,1)')
expected_basis=[f'0{t}','01']
assert_true(al['basis_edges']==expected_basis, f"basis_edges {al['basis_edges']} != {expected_basis}")
assert_true(term['terminal_carrier']['edges']==expected_basis, 'terminal carrier edges do not match alignment basis')
# basis independent in A8: 06 and 01 are distinct star edges.
assert_true(len(set(al['basis_edges']))==2, 'terminal basis has duplicate edges')

# 2. Terminal A2 row-vector semantics.
vecs=[tuple(x) for x in al['rows']]
standard={(-1,0),(1,1),(0,-1)}
assert_true(set(vecs)==standard, f'terminal rows {vecs} are not the standard signed A2 rows {standard}')
assert_true(tuple(sum(v[i] for v in vecs) for i in (0,1))==(0,0), 'terminal A2 row vectors do not sum to zero')
for a,b in itertools.combinations(vecs,2):
    assert_true(abs(det(a,b))==1, f'terminal A2 determinant not primitive: {a},{b}, det={det(a,b)}')
perm=al['permutation']; signs=al['signs']
assert_true(sorted(perm)==[0,1,2], 'terminal permutation is not S3')
assert_true(all(s in (-1,1) for s in signs), 'terminal signs are not ±1')

# 3. Recompute the standard terminal A2 word on sample even moduli.
a=[(1,0),(0,1),(0,0)]
p=(1,2); eH=(1,0); eV=(0,1); eD=(-1,1)
words={
    'id': (0,1,2),
    'tau02': (2,1,0),
    'tau12': (0,2,1),
    'tau01': (1,0,2),
    'chi+': (1,2,0),
    'chi-': (2,0,1),
}
Deltas=[(0,1),(1,0),(1,-1)]

def omega(q,m):
    x,y=q
    # center remains default
    if (x%m,y%m)==(p[0]%m,p[1]%m):
        return words['id']
    # H line p + t(1,0): y=2
    if y%m==p[1]%m:
        t=(x-p[0])%m
        if t==1%m: return words['chi+']
        if t==(-1)%m: return words['chi-']
        if t!=0: return words['tau02']
    # V line p + t(0,1): x=1
    if x%m==p[0]%m:
        t=(y-p[1])%m
        if t==1%m: return words['chi-']
        if t==(-1)%m: return words['chi+']
        if t!=0: return words['tau12']
    # D line p + t(-1,1): x+y=3
    if (x+y-p[0]-p[1])%m==0:
        # t = y-p_y = -(x-p_x)
        t=(y-p[1])%m
        if t==1%m: return words['chi+']
        if t==(-1)%m: return words['chi-']
        if t!=0: return words['tau01']
    return words['id']

def eta(i,z,m):
    # eta_i(z)=(z-a_i)+a_{omega(z-a_i)_i}
    q=sub2(z,a[i],m)
    w=omega(q,m)
    return add2(q,a[w[i]],m)

def F(i,z,m):
    return eta(i,add2(z,Deltas[i],m),m)

def orbit_len(f,start,m):
    seen=[]; z=start
    while z not in seen:
        seen.append(z); z=f(z)
    return len(seen), z, seen

sample_moduli=[4,6,8,10,12,14]
for m in sample_moduli:
    for i in range(3):
        n,end,orb=orbit_len(lambda z,i=i: F(i,z,m),(0,0),m)
        assert_true(end==(0,0) and n==m*m and len(set(orb))==m*m,
                    f'terminal F_{i} not one cycle in sample m={m}: n={n}, end={end}')
    if m>=6:
        L=m-1
        C=[None]*L
        C[0]=(0,0); C[1]=((-1)%m,1%m)
        for j in range(2,L): C[j]=((-j-1)%m,j%m)
        assert_true(len(set(C))==L and math.gcd(L,m)==1, f'bad selector C_m for m={m}')
        F1_inv={F(1,z,m):z for z in itertools.product(range(m), repeat=2)}
        for j,c in enumerate(C):
            nxt=F1_inv[F(0,c,m)]
            assert_true(nxt==C[(j+1)%L], f'interlacing F1^-1 F0 failure m={m}, j={j}, got {nxt}, want {C[(j+1)%L]}')
    else:
        # Small marked parent at m=4 uses pair F1,F2 and C4 from the terminal theorem.
        C4=[(0,3),(3,0),(3,3)]
        F2_inv={F(2,z,4):z for z in itertools.product(range(4), repeat=2)}
        got=[F2_inv[F(1,c,4)] for c in C4]
        assert_true(got==[C4[1],C4[2],C4[0]], f'm=4 small selector mismatch: {got}')

print('OK: D9 terminal A2 block semantics verified')
print('terminal shifted triple:', rows[-1]['triple'], 'height:', shifts[-1], 'chronological:', chron)
print('terminal basis:', al['basis_edges'], 'A2 rows:', vecs)
print('sample terminal returns checked for m=', sample_moduli)
