#!/usr/bin/env python3
import json, sys
D=9
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
CERT=str(ROOT/'certificates'/'d9_terminal_reserve_frame_candidate.json')
LEDGER=str(ROOT/'certificates'/'d9_affine_splice_placement_ledger.json')

def edge_vec(e):
    if isinstance(e,str):
        i=int(e[0]); j=int(e[1])
    else:
        i,j=e
    v=[0]*D; v[i]-=1; v[j]+=1; return v

def dot(a,b): return sum(x*y for x,y in zip(a,b))
def sub(a,b): return [x-y for x,y in zip(a,b)]
def add(a,b): return [x+y for x,y in zip(a,b)]
def smul(k,v): return [k*x for x in v]
def assert_true(cond,msg):
    if not cond:
        raise AssertionError(msg)

def rank_edges(edges):
    # rank over Q by simple Gaussian using vectors in Q floats? exact fractions unnecessary small ints use sympy? no dependency.
    import fractions
    mat=[[fractions.Fraction(x) for x in edge_vec(e)] for e in edges]
    r=0; rows=len(mat); cols=D
    for c in range(cols):
        piv=None
        for i in range(r,rows):
            if mat[i][c]!=0:
                piv=i; break
        if piv is None: continue
        mat[r],mat[piv]=mat[piv],mat[r]
        pv=mat[r][c]
        mat[r]=[x/pv for x in mat[r]]
        for i in range(rows):
            if i!=r and mat[i][c]!=0:
                f=mat[i][c]
                mat[i]=[mat[i][j]-f*mat[r][j] for j in range(cols)]
        r+=1
        if r==rows: break
    return r

cert=json.load(open(CERT))
ledger=json.load(open(LEDGER))
# reconstruct objects from ledger and compare names in cert
objects=[]
for st in ledger['stages']:
    for part in st['parts']:
        objects.append({
            'name': f"r{st['stage']}_p{part['part_index']}_P{part['P']}",
            'base': part['basepoint'],
            'edges': part['active_edges']
        })
obj_by_name={o['name']:o for o in objects}

# terminal plane
T=cert['terminal_carrier']
R=cert['reserve_plane']
assert_true(sum(T['base'])==0, 'terminal base not root-flat')
assert_true(sum(R['base'])==0, 'reserve base not root-flat')
assert_true(rank_edges(T['edges'])==2, 'terminal edges rank not 2')
assert_true(rank_edges(R['edges'])==2, 'reserve edges rank not 2')
assert_true(T['edges']==cert['terminal_alignment']['basis_edges'], 'terminal basis mismatch')
assert_true([(x+cert['terminal_alignment']['height_shift'])%D for x in cert['terminal_alignment']['terminal_triple_chronological']]==cert['terminal_alignment']['root_vertices'], 'terminal shifted root vertices mismatch')

# validate separation blocks. For all even m>9, if abs(diff)<=9 and nonzero then diff != 0 mod m.
def check_sep(A_base,A_edges,B_base,B_edges,sep,what):
    w=sep['w']; diff=sep['diff']
    assert_true(len(w)==D, what+': bad w length')
    for e in A_edges:
        assert_true(dot(w,edge_vec(e))==0, what+f': w not zero on A edge {e}')
    for e in B_edges:
        assert_true(dot(w,edge_vec(e))==0, what+f': w not zero on B edge {e}')
    actual=dot(w,sub(A_base,B_base))
    assert_true(actual==diff, what+f': diff mismatch {actual} != {diff}')
    assert_true(diff!=0 and abs(diff)<=9, what+f': diff not high-even safe: {diff}')

# terminal vs splices
assert_true(len(T['separations'])==len(objects), 'wrong number terminal separations')
for entry in T['separations']:
    o=obj_by_name[entry['name']]
    check_sep(T['base'],T['edges'],o['base'],o['edges'],entry['separator'],'terminal/'+entry['name'])
# reserve vs splices and terminal
assert_true(len(R['separations'])==len(objects)+1, 'wrong number reserve separations')
for entry in R['separations']:
    if entry['name']=='terminal_carrier':
        o={'base':T['base'],'edges':T['edges']}
    else:
        o=obj_by_name[entry['name']]
    check_sep(R['base'],R['edges'],o['base'],o['edges'],entry['separator'],'reserve/'+entry['name'])

# reserve sites
sites=cert['reserve_sites']
assert_true(len(sites)==12, 'need D+3=12 reserve sites')
vecs=[edge_vec(e) for e in R['edges']]
seen_coeff=set()
for s in sites:
    a,b=s['coeff']
    seen_coeff.add((a,b))
    expected=add(R['base'], add(smul(a,vecs[0]), smul(b,vecs[1])))
    assert_true(expected==s['point'], 'site point mismatch '+s['name'])
    assert_true(sum(s['point'])==0, 'site not root-flat '+s['name'])
# distinct for all even m>9: coefficient pairs in [0,3]x[0,2], basis vectors independent and coefficient differences have abs < 10.
assert_true(len(seen_coeff)==12, 'duplicate coefficients')
for i in range(len(sites)):
    for j in range(i+1,len(sites)):
        diff=[sites[i]['point'][k]-sites[j]['point'][k] for k in range(D)]
        assert_true(any(x!=0 for x in diff), 'identical integer reserve sites')
        assert_true(max(abs(x) for x in diff)<10, 'site difference not small')
# Ensure reserve sites separated using same separator certs: since each site lies in reserve plane, already implied. Check terminal carrier plane too.
print('OK: D9 terminal/reserve frame verified')
print('terminal base=',T['base'],'edges=',T['edges'],'separations=',len(T['separations']))
print('reserve base=',R['base'],'edges=',R['edges'],'separations=',len(R['separations']),'sites=',len(sites))
print('terminal alignment=',cert['terminal_alignment'])
print('max terminal sep diff=',max(abs(e['separator']['diff']) for e in T['separations']))
print('max reserve sep diff=',max(abs(e['separator']['diff']) for e in R['separations']))
