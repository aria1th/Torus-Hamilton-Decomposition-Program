#!/usr/bin/env python3
"""Independent stdlib verifier for the D9 high-even certificates.

JSON encoding, read before writing this verifier:
- active stages are `rows_shifted[i]`, each row containing one `triple` and
  three `pairs` on labels 0..8; the same row/part is addressed by
  `active_data[i]["parts"][j]` and `supports_unshifted[i]["parts"][j]`.
- edges are either two-label lists `[a,b]` or strings `"ab"`; directed affine
  edge `ab` means the root vector e_b - e_a.
- ledger stages are `stages[i]`; each part records a basepoint, active edges,
  support edges, band value, and per-color descendant-coordinate data.
"""
import itertools, json, os, sys

ROOT = os.path.dirname(os.path.abspath(__file__))
D = 9
A = json.load(open(os.path.join(ROOT, "certificates/d9_active_anchor_candidate_v1.json")))
L = json.load(open(os.path.join(ROOT, "certificates/d9_affine_splice_placement_ledger.json")))
F = json.load(open(os.path.join(ROOT, "certificates/d9_terminal_reserve_frame_candidate.json")))
ASSUMPTIONS, MISMATCHES, CONSTANTS = [], [], []

def assumption(s):
    if s not in ASSUMPTIONS: ASSUMPTIONS.append(s)
def mismatch(s):
    if s not in MISMATCHES: MISMATCHES.append(s)
def bad(fails, path, msg, mm=False):
    s = f"{path}: {msg}"; fails.append(s)
    if mm: mismatch(s)
def const(where, value): CONSTANTS.append((abs(value), value, where))
def es(e):
    if isinstance(e, str): return e
    return "%d%d" % (e[0], e[1])
def ee(e): s = es(e); return int(s[0]), int(s[1])
def ue(e): a,b = ee(e); return "%d%d" % tuple(sorted((a,b)))
def de(w,e): a,b = ee(e); return w[b] - w[a]
def der(labels,e):
    labels = set(labels); a,b = ee(e)
    return (1 if b in labels else 0) - (1 if a in labels else 0)
def dot(a,b): return sum(x*y for x,y in zip(a,b))
def sub(a,b): return [x-y for x,y in zip(a,b)]
def add_edge(p,e,k):
    p = list(p); a,b = ee(e); p[a] -= k; p[b] += k; return p
def det(u,v): return u[0]*v[1] - u[1]*v[0]

class DSU:
    def __init__(self,n): self.p = list(range(n))
    def f(self,x):
        while self.p[x] != x:
            self.p[x] = self.p[self.p[x]]; x = self.p[x]
        return x
    def u(self,a,b):
        a,b = self.f(a), self.f(b)
        if a == b: return False
        self.p[b] = a; return True

def increments(fails):
    inc = {}
    if len(A.get("rows_shifted", [])) != 7 or len(A.get("active_data", [])) != 7:
        bad(fails, "$.rows_shifted/active_data", "expected seven stages", True); return inc
    for i,(row,shift,ad) in enumerate(zip(A["rows_shifted"], A["shifts"], A["active_data"])):
        parts, tri, pairs = ad.get("parts", []), row.get("triple"), row.get("pairs")
        if len(parts) != 4 or not (isinstance(tri,list) and len(tri)==3) or not (isinstance(pairs,list) and len(pairs)==3):
            bad(fails, f"stage {i+1}", "expected one triple part and three pair parts"); continue
        exp = [(x-shift) % D for x in tri]
        if parts[0].get("P") != exp:
            bad(fails, f"$.active_data[{i}].parts[0].P", f"expected {exp}, found {parts[0].get('P')}", True)
        for k,c in enumerate(parts[0].get("P", [])):
            inc[(i,c)] = (tri[k], tri[(k+1)%3], ue([tri[k], tri[(k+1)%3]]))
        for j,pair in enumerate(pairs, 1):
            exp = [(pair[0]-shift) % D, (pair[1]-shift) % D]
            if parts[j].get("P") != exp:
                bad(fails, f"$.active_data[{i}].parts[{j}].P", f"expected {exp}, found {parts[j].get('P')}", True)
            if parts[j].get("physical_edge") != pair:
                bad(fails, f"$.active_data[{i}].parts[{j}].physical_edge", f"expected {pair}, found {parts[j].get('physical_edge')}", True)
            p = parts[j].get("P", [])
            if len(p) == 2:
                inc[(i,p[0])] = (pair[0], pair[1], ue(pair))
                inc[(i,p[1])] = (pair[1], pair[0], ue(pair))
    return inc

def c1a(f):
    if A.get("D") != D: bad(f, "$.D", f"expected 9, found {A.get('D')}", True)
    rows = A.get("rows_shifted", [])
    if len(rows) != 7: bad(f, "$.rows_shifted", f"expected 7 rows, found {len(rows)}", True)
    for i,r in enumerate(rows):
        if set(r) != {"triple","pairs"}: bad(f, f"$.rows_shifted[{i}]", f"expected keys triple,pairs; found {sorted(r)}", True)
        labels = list(r.get("triple", [])) + [x for p in r.get("pairs", []) for x in p]
        if len(r.get("triple", [])) != 3 or len(r.get("pairs", [])) != 3 or sorted(labels) != list(range(D)):
            bad(f, f"$.rows_shifted[{i}]", f"not one triple plus three pairs on Z/9: {labels}")
    return "7 stages; each row has 1 triple + 3 pairs on 9 labels"

def c1b(f):
    assumption("C1b ASSUMPTION: active JSON has no final forest/closing-edge field; reconstruct one directed row edge per color/stage from rows_shifted and active_data, then close by isolate->color.")
    mismatch("C1b encoding note: no explicit final_forests/closing_edges field is present in certificates/d9_active_anchor_candidate_v1.json.")
    inc, isolates, closings, nedge = increments(f), [], [], 0
    for c in range(D):
        edges, directed = [], []
        for i in range(7):
            if (i,c) not in inc: bad(f, f"stage {i+1} color {c}", "missing row edge"); continue
            a,b,u = inc[(i,c)]; edges.append(u); directed.append(f"{a}->{b}")
        nedge += len(edges); d, deg, cyc = DSU(D), [0]*D, False
        for e in edges:
            a,b = ee(e); deg[a] += 1; deg[b] += 1
            if not d.u(a,b): cyc = True
        comps = {}
        for v in range(D): comps.setdefault(d.f(v), []).append(v)
        iso, sizes = [v for v in range(D) if deg[v] == 0], sorted(len(x) for x in comps.values())
        if cyc or len(iso) != 1 or sizes != [1,8]:
            bad(f, f"color {c} final graph", f"expected one-isolate tree; edges={edges} directed={directed} components={sizes} cycle={cyc}"); continue
        isolates.append(iso[0]); closings.append(f"{iso[0]}->{c}")
        d2, cyc2 = DSU(D), False
        for e in edges + [ue([iso[0], c])]:
            a,b = ee(e)
            if not d2.u(a,b): cyc2 = True
        if cyc2 or len({d2.f(v) for v in range(D)}) != 1: bad(f, f"color {c} closing edge", f"{iso[0]}->{c} is not spanning-tree closing")
    return f"9 color forests; row_edges={nedge}; isolates={isolates}; closings={closings}"

def c1c(f):
    n = 0
    for i,st in enumerate(A.get("active_data", [])):
        for j,p in enumerate(st.get("parts", [])):
            if p.get("kind") == "pair_unit":
                n += 1; vals = p.get("lambda_values")
                if not (isinstance(vals,list) and len(vals)==2 and all(x in (-1,1) for x in vals)):
                    bad(f, f"$.active_data[{i}].parts[{j}].lambda_values", f"expected two +/-1 values, found {vals}")
    if n != 21: bad(f, "$.active_data", f"expected 21 pair_unit parts, found {n}")
    return "21 pair rows; all lambda increments are +/-1"

def c1d(f):
    ds = []
    for i,st in enumerate(A.get("active_data", [])[:6]):
        p = st.get("parts", [{}])[0]; vecs = p.get("vectors")
        if p.get("kind") != "triple_active" or not (isinstance(vecs,list) and len(vecs)==3 and all(len(v)==2 for v in vecs)):
            bad(f, f"$.active_data[{i}].parts[0]", "expected triple_active with three Z^2 vectors"); continue
        for u,v in itertools.combinations(vecs, 2):
            d = det(u,v); ds.append(d)
            if d not in (-1,1): bad(f, f"$.active_data[{i}].parts[0].vectors", f"det({u},{v})={d}")
    return f"6 nonterminal triples; determinants={ds}"

def c1e(f):
    final = A.get("rows_shifted", [{}])[-1].get("triple")
    if final != [6,0,1]: bad(f, "$.rows_shifted[6].triple", f"expected [6,0,1], found {final}")
    return f"final shifted triple={final}"

def trace_map():
    return {(st.get("stage"), p.get("part_index")):(p.get("basepoint"), p.get("active_edges")) for st in L.get("stages", []) for p in st.get("parts", [])}

def c2a(f):
    inc, prev = increments(f), {c:[] for c in range(D)}
    if L.get("D") != D: bad(f, "$.D", f"expected 9, found {L.get('D')}", True)
    inactive = supports = colors = 0
    for i,st in enumerate(L.get("stages", [])):
        if st.get("stage") != i+1: bad(f, f"$.stages[{i}].stage", f"expected {i+1}", True)
        if st.get("height_shift") != A["shifts"][i]: bad(f, f"$.stages[{i}].height_shift", f"expected {A['shifts'][i]}, found {st.get('height_shift')}", True)
        for j,part in enumerate(st.get("parts", [])):
            supports += 1; path = f"$.stages[{i}].parts[{j}]"
            ap, sp = A["active_data"][i]["parts"][j], A["supports_unshifted"][i]["parts"][j]
            if part.get("P") != ap.get("P") or part.get("P") != sp.get("P"): bad(f, path+".P", f"ledger/active/support mismatch {part.get('P')} / {ap.get('P')} / {sp.get('P')}", True)
            sedges = [es(e) for e in sp.get("M", [])]
            if part.get("support_edges") != sedges: bad(f, path+".support_edges", f"expected {sedges}, found {part.get('support_edges')}", True)
            kind = ap.get("kind")
            if kind == "triple_active": aedges = [es(e) for e in ap.get("active_edges", [])]
            elif kind == "pair_unit": aedges = [es(ap.get("physical_edge"))]
            elif kind == "terminal_triple_basic":
                assumption("C2a ASSUMPTION: stage-7 terminal_triple_basic has no A2 witness in active JSON; ledger is checked as one-dimensional terminal support with unit scalar active vectors.")
                aedges = part.get("active_edges", [])
                if not (len(aedges)==1 and aedges == part.get("support_edges")): bad(f, path+".active_edges", "terminal support should have one active support edge")
            else: aedges = []; bad(f, f"$.active_data[{i}].parts[{j}].kind", f"unknown kind {kind}", True)
            if part.get("active_edges") != aedges: bad(f, path+".active_edges", f"expected {aedges}, found {part.get('active_edges')}", True)
            base = part.get("basepoint", [])
            if len(base) != D or sum(base) != 0: bad(f, path+".basepoint", f"expected root-flat length-9 vector, found {base}")
            for k,cd in enumerate(part.get("colors", [])):
                colors += 1; cpath = f"{path}.colors[{k}]"; c = cd.get("color")
                if k < len(part.get("P", [])) and c != part["P"][k]: bad(f, cpath+".color", f"expected {part['P'][k]}, found {c}", True)
                if (i,c) in inc and cd.get("physical_increment") != f"{inc[(i,c)][0]}->{inc[(i,c)][1]}": bad(f, cpath+".physical_increment", f"expected {inc[(i,c)][0]}->{inc[(i,c)][1]}, found {cd.get('physical_increment')}", True)
                if cd.get("previous_forest") != prev.get(c, []): bad(f, cpath+".previous_forest", f"expected {prev.get(c, [])}, found {cd.get('previous_forest')}", True)
                want = ap.get("vectors", [None]*3)[k] if kind == "triple_active" else ([ap.get("lambda_values", [None]*2)[k]] if kind == "pair_unit" else None)
                if want is None:
                    av = cd.get("active_vector")
                    if not (isinstance(av,list) and len(av)==1 and av[0] in (-1,1)): bad(f, cpath+".active_vector", f"expected scalar unit, found {av}")
                elif cd.get("active_vector") != want: bad(f, cpath+".active_vector", f"expected {want}, found {cd.get('active_vector')}", True)
                coords = cd.get("support_coordinates", [])
                if [x.get("edge") for x in coords] != part.get("support_edges", []): bad(f, cpath+".support_coordinates", "coordinate edge list differs from support_edges", True)
                for m,co in enumerate(coords):
                    vals, edge = co.get("active_direction_values", {}), co.get("edge")
                    if set(vals) != set(aedges): bad(f, f"{cpath}.support_coordinates[{m}].active_direction_values", f"expected keys {aedges}, found {sorted(vals)}", True)
                    for ae in aedges:
                        wantd = der(co.get("descendant_labels", []), ae)
                        if vals.get(ae) != wantd: bad(f, f"{cpath}.support_coordinates[{m}].active_direction_values[{ae}]", f"expected derivative {wantd}, found {vals.get(ae)}")
                        if edge not in aedges:
                            inactive += 1
                            if vals.get(ae) != 0: bad(f, f"{cpath}.support_coordinates[{m}]", f"inactive coordinate {edge} varies along {ae}")
                for ae in aedges:
                    if der(cd.get("omitted_labels", []), ae) != 0: bad(f, cpath+".omitted_labels", f"omitted coordinate varies along {ae}")
        for c in range(D):
            if (i,c) in inc: prev[c].append(inc[(i,c)][2])
    return f"28 supports; 63 color traces; inactive derivatives checked={inactive}"

def c2b(f):
    assumption("C2b ASSUMPTION: ledger has one height_shift per stage, not per part; distinctness is checked for the seven stage heights used by splice rows.")
    mismatch("C2b wording/encoding note: certificates/d9_affine_splice_placement_ledger.json stores `height_shift` at stage level; individual parts do not have separate height fields.")
    hs, mx, where = [st.get("height_shift") for st in L.get("stages", [])], 0, None
    for (i,a),(j,b) in itertools.combinations(list(enumerate(hs,1)), 2):
        d = a-b; const(f"C2b height r{i}={a} vs r{j}={b}", d)
        if d == 0 or abs(d) > 9: bad(f, "$.stages[*].height_shift", f"bad height diff {d} for stages {i},{j}")
        if abs(d) > mx: mx, where = abs(d), f"r{i}={a} vs r{j}={b}"
    return f"heights={hs}; max pairwise |diff|={mx} at {where}"

def c2c(f):
    vals_all = []
    for i,st in enumerate(L.get("stages", [])):
        w, vals = st.get("band_functional"), []
        if len(w) != D: bad(f, f"$.stages[{i}].band_functional", f"expected length 9, found {w}", True); continue
        for e in st.get("active_graph_edges", []):
            if de(w,e) != 0: bad(f, f"$.stages[{i}].band_functional", f"varies on active graph edge {e}")
        for p in st.get("parts", []):
            for e in p.get("active_edges", []):
                if de(w,e) != 0: bad(f, f"$.stages[{i}].parts[{p.get('part_index')}].active_edges", f"band varies along {e}")
            val = dot(w, p.get("basepoint", [0]*D)); vals.append(val)
            if val != p.get("band_value"): bad(f, f"$.stages[{i}].parts[{p.get('part_index')}].band_value", f"expected {val}, found {p.get('band_value')}", True)
        if len(set(vals)) != len(vals): bad(f, f"$.stages[{i}].parts[*].band_value", f"not distinct: {vals}")
        for a,b in itertools.combinations(vals,2): const(f"C2c band stage {st.get('stage')} values {a} vs {b}", a-b)
        vals_all.append(tuple(vals))
    return f"7 row bands; per-stage values={vals_all}"

def c3a(f):
    qt, qr = [0,0,2,2,-4,0,0,0,0], [3,4,3,5,-15,0,0,0,0]
    t, r = F.get("terminal_carrier", {}), F.get("reserve_plane", {})
    if F.get("D") != D: bad(f, "$.D", f"expected 9, found {F.get('D')}", True)
    if t.get("base") != qt or t.get("edges") != ["06","01"]: bad(f, "$.terminal_carrier", f"expected q_T+<06,01>, found {t}", True)
    if r.get("base") != qr or r.get("edges") != ["24","35"]: bad(f, "$.reserve_plane", f"expected q_R+<24,35>, found {r}", True)
    al = F.get("terminal_alignment", {})
    if al.get("root_vertices") != [6,0,1] or al.get("basis_edges") != ["06","01"]: bad(f, "$.terminal_alignment", "terminal root/basis alignment mismatch", True)
    exp = [(a,b) for b in range(3) for a in range(4)]
    coeffs = [tuple(s.get("coeff", [])) for s in F.get("reserve_sites", [])]
    if coeffs != exp: bad(f, "$.reserve_sites[*].coeff", f"expected {exp}, found {coeffs}", True)
    for i,s in enumerate(F.get("reserve_sites", [])):
        p = add_edge(add_edge(qr, "24", s.get("coeff", [0,0])[0]), "35", s.get("coeff", [0,0])[1])
        if s.get("point") != p: bad(f, f"$.reserve_sites[{i}].point", f"expected {p}, found {s.get('point')}", True)
    return f"q_T/q_R verified; terminal edges=06,01; reserve grid sites={len(F.get('reserve_sites', []))}"

def sep_check(f, fam, main_base, main_edges, sep, traces):
    w, diff = sep.get("separator", {}).get("w"), sep.get("separator", {}).get("diff")
    name = f"{fam} {sep.get('name')}"
    if not (isinstance(w,list) and len(w)==D): bad(f, name+".separator.w", f"expected length 9, found {w}", True); return None
    for e in main_edges + sep.get("edges", []):
        if de(w,e) != 0: bad(f, name+".separator.w", f"does not vanish on {e}")
    calc = dot(w, sub(main_base, sep.get("base", [0]*D)))
    if calc != diff: bad(f, name+".separator.diff", f"expected {calc}, found {diff}", True)
    if not isinstance(diff,int) or diff == 0 or abs(diff) > 9: bad(f, name+".separator.diff", f"expected nonzero integer abs<=9, found {diff}")
    if sep.get("stage") != "T":
        key = (sep.get("stage"), sep.get("part_index"))
        if key not in traces: bad(f, name, f"no matching ledger trace for {key}", True)
        elif sep.get("base") != traces[key][0] or sep.get("edges") != traces[key][1]: bad(f, name, f"trace base/edges mismatch for {key}", True)
    const(name, diff); return diff

def c3b(f):
    traces, t, r = trace_map(), F["terminal_carrier"], F["reserve_plane"]
    ts, rs = t.get("separations", []), r.get("separations", [])
    if len(ts) != 28: bad(f, "$.terminal_carrier.separations", f"expected 28 rows, found {len(ts)}", True)
    if len(rs) != 29: bad(f, "$.reserve_plane.separations", f"expected 29 rows, found {len(rs)}", True)
    maxs, seen_t, seen_r = {"terminal-splice":0,"reserve-splice":0,"terminal-reserve":0}, set(), set()
    for s in ts:
        d = sep_check(f, "terminal-splice", t["base"], t["edges"], s, traces); seen_t.add((s.get("stage"), s.get("part_index")))
        if isinstance(d,int): maxs["terminal-splice"] = max(maxs["terminal-splice"], abs(d))
    for s in rs:
        if s.get("stage") == "T":
            d = sep_check(f, "terminal-reserve", r["base"], r["edges"], s, traces)
            if s.get("base") != t["base"] or s.get("edges") != t["edges"]: bad(f, "reserve terminal_carrier separation", "terminal base/edges mismatch", True)
            if isinstance(d,int): maxs["terminal-reserve"] = max(maxs["terminal-reserve"], abs(d))
        else:
            d = sep_check(f, "reserve-splice", r["base"], r["edges"], s, traces); seen_r.add((s.get("stage"), s.get("part_index")))
            if isinstance(d,int): maxs["reserve-splice"] = max(maxs["reserve-splice"], abs(d))
    if seen_t != set(traces): bad(f, "$.terminal_carrier.separations", "does not cover all ledger traces", True)
    if seen_r != set(traces): bad(f, "$.reserve_plane.separations", "does not cover all ledger traces", True)
    return "max |diff| terminal-splice=%d, reserve-splice=%d, terminal-reserve=%d" % (maxs["terminal-splice"], maxs["reserve-splice"], maxs["terminal-reserve"])

def c3c(f):
    r, t = F["reserve_plane"], F["terminal_carrier"]
    rows = [s for s in r.get("separations", []) if s.get("stage") == "T"]
    if len(rows) != 1: bad(f, "$.reserve_plane.separations", f"expected one terminal-reserve row, found {len(rows)}", True); return f"terminal-reserve rows={len(rows)}"
    s, w, diff = rows[0], rows[0]["separator"]["w"], rows[0]["separator"]["diff"]
    for e in r["edges"] + t["edges"]:
        if de(w,e) != 0: bad(f, "terminal-reserve.separator.w", f"does not vanish on {e}")
    if dot(w, sub(r["base"], t["base"])) != diff or diff == 0: bad(f, "terminal-reserve.separator.diff", f"bad diff {diff}")
    return f"separator w={w}; diff={diff} proves disjoint over Z"

def c4(f):
    if not CONSTANTS: bad(f, "uniform constants", "none collected"); return "no constants collected"
    mx, val, where = max(CONSTANTS, key=lambda x: x[0])
    if mx > 9: bad(f, "uniform constants", f"global max {mx} exceeds 9 at {where}")
    zeros = [(v,w) for _,v,w in CONSTANTS if v == 0]
    if zeros: bad(f, "uniform constants", f"zero nonvanishing constants found: {zeros[:3]}")
    return f"constants={len(CONSTANTS)}; global max |value|={mx} at {where} (value={val})"

CHECKS = [("C1a",c1a),("C1b",c1b),("C1c",c1c),("C1d",c1d),("C1e",c1e),("C2a",c2a),("C2b",c2b),("C2c",c2c),("C3a",c3a),("C3b",c3b),("C3c",c3c),("C4",c4)]

def run():
    rows, failures = [], {}
    for cid, fn in CHECKS:
        fs = []
        try: ev = fn(fs)
        except Exception as e: fs.append(f"{cid} raised {type(e).__name__}: {e}"); ev = "exception during check"
        if fs: ev += f"; failures={len(fs)}; first={fs[0]}"; failures[cid] = fs
        rows.append((cid, "PASS" if not fs else "FAIL", ev))
    return rows, failures

def render(rows, failures):
    out = ["# Independent D9 Verdict", "", "| check id | PASS/FAIL | one-line numeric evidence |", "|---|---|---|"]
    out += [f"| {cid} | {st} | {str(ev).replace('|','\\|')} |" for cid,st,ev in rows]
    out += ["", "## ASSUMPTIONs"]
    out += ["- "+x for x in ASSUMPTIONS] if ASSUMPTIONS else ["- None."]
    out += ["", "## Mismatches / Encoding Notes"]
    out += ["- "+x for x in MISMATCHES] if MISMATCHES else ["- None."]
    if failures:
        out += ["", "## Failure Details"]
        for cid in sorted(failures):
            out += [f"- {cid}: {x}" for x in failures[cid]]
    out += ["", "Overall verdict: " + ("PASS" if not failures else "FAIL")]
    return "\n".join(out) + "\n"

if __name__ == "__main__":
    rows, failures = run(); text = render(rows, failures)
    print(text, end="")
    open(os.path.join(ROOT, "INDEPENDENT_VERDICT.md"), "w", encoding="utf-8").write(text)
    sys.exit(0 if not failures else 1)
