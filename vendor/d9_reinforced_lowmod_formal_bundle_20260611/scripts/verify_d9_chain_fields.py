#!/usr/bin/env python3
"""Verify D9 -> D11 high-even chain-field assembly.

This checks the non-root-flat metadata needed to feed the direct D9 anchor into
the corrected ordinary paired growth step.  It does not reconstruct D11; it
checks the label chart, terminal-carrier disjointness, fixed-old reserve form,
and midpoint-collision phase avoidance for the two ordinary paired rows.
"""
import json
from pathlib import Path
D=9; N=11
ROOT=Path(__file__).resolve().parent
DATA_DIR=ROOT.parent if ROOT.name=='scripts' else ROOT
def pick(*parts):
    p=DATA_DIR.joinpath(*parts)
    if p.exists(): return p
    return Path('/mnt/data').joinpath(parts[-1])
CHAIN=pick('certificates','d9_chain_fields_candidate.json')
ACTIVE=pick('certificates','d9_active_anchor_candidate_v1.json')
TERM=pick('certificates','d9_terminal_reserve_frame_candidate.json')
chain=json.loads(CHAIN.read_text())
active=json.loads(ACTIVE.read_text())
term=json.loads(TERM.read_text())

def assert_true(cond,msg):
    if not cond: raise AssertionError(msg)

def inv_mod(a,n):
    for x in range(n):
        if a*x%n==1: return x
    raise ValueError

def midpoint(a,b,n=N):
    return ((a+b)*inv_mod(2,n))%n
assert_true(chain['D']==D and chain['next_D']==N, 'wrong D/next_D')
emb={int(k):v for k,v in chain['label_chart']['old_label_embedding'].items()}
assert_true(sorted(emb)==list(range(D)), 'embedding domain not Z/9Z')
assert_true(sorted(emb.values())==[1,2,4,5,6,7,8,9,10], 'embedding image not Z/11Z minus {0,3}')
assert_true(set(chain['label_chart']['new_labels'])=={0,3}, 'new labels not {0,3}')
# terminal carrier alignment and disjointness from growth window labels.
source_carrier=term['terminal_alignment']['root_vertices']
assert_true(source_carrier==chain['terminal_carrier']['source_labels'], 'source terminal carrier mismatch')
target_carrier=[emb[x] for x in source_carrier]
assert_true(target_carrier==chain['terminal_carrier']['target_labels'], 'target terminal carrier mismatch')
growth_window=set()
for row in chain['ordinary_paired_growth_interface']:
    growth_window.update(row['labels_mod_11'])
assert_true(growth_window=={0,1,2,3,4,9,10}, f'ordinary growth window unexpected: {growth_window}')
assert_true(set(target_carrier).isdisjoint(growth_window), f'terminal carrier {target_carrier} meets growth window {growth_window}')
# reserve edges transported to old labels only.
for ew in chain['endpoint_reserve_transport']['target_plane_edges']:
    a=int(ew[:-1]) if len(ew)>2 else int(ew[0])
    b=int(ew[-1])
    assert_true(a not in (0,3) and b not in (0,3), f'reserve target edge uses new label: {ew}')
roles=chain['endpoint_reserve_transport']['reserve_roles']
assert_true(roles==['U0','U1','U2']+[f'U{j}_c' for j in range(1,9)]+['U_star'], 'reserve roles mismatch')
# midpoint collision sets and phase avoidance.
assert_true(chain['midpoint_translate_rule']['inverse_of_2_mod_11']==inv_mod(2,N), 'bad inverse of two')
for row in chain['ordinary_paired_growth_interface']:
    one=row['cut_one_side_old']; zero=row['cut_zero_side_old']
    C=sorted({midpoint(a,b) for a in one for b in zero})
    assert_true(sorted(row['midpoint_collision_set'])==C, f'{row["name"]}: bad collision set {row["midpoint_collision_set"]}, expected {C}')
    rho=row['chosen_phase']%N
    centers=sorted({(rho-1)%N,rho,(rho+1)%N})
    assert_true(sorted(row['phase_centers'])==centers, f'{row["name"]}: phase centers mismatch')
    assert_true(set(centers).isdisjoint(C), f'{row["name"]}: phase centers {centers} hit midpoint collision set {C}')
    # leaf lines use one new and one old label; quotient direction is old-old.
    leaf=[int(x) for x in row['leaf_line']]
    qdir=[int(x) for x in row['quotient_direction']]
    assert_true(len(set(leaf))==2 and len(set(qdir))==2, f'{row["name"]}: degenerate lines')
    assert_true(any(x in (0,3) for x in leaf), f'{row["name"]}: leaf line does not use a new label')
    assert_true(all(x not in (0,3) for x in qdir), f'{row["name"]}: quotient direction is not old-old')
print('OK: D9 high-even chain fields verified')
print('old-label embedding:', emb)
print('terminal carrier target labels:', target_carrier)
for row in chain['ordinary_paired_growth_interface']:
    print(f"{row['name']}: C={row['midpoint_collision_set']} phase={row['chosen_phase']} centers={row['phase_centers']}")
