import json,itertools,collections
D=9
cert=json.load(open('/mnt/data/d9_anchor_candidate.json'))
shifts=cert['shifts']

def norm(e): return tuple(sorted(e))
def row_perm(row):
 p=list(range(D)); a,b,c=row['triple']; p[a]=b;p[b]=c;p[c]=a
 for x,y in row['pairs']: p[x]=y;p[y]=x
 return p
perms=[row_perm(r) for r in cert['rows_shifted']]
r=4; P=(8,7,0); s=shifts[r]; p=perms[r]
# prev comps
prev={}
for color in P:
    edges=[]
    for rr in range(r):
        tail=(color+shifts[rr])%D; edges.append(norm((tail,perms[rr][tail])))
    prev[color]=edges

def dsu(n,edges):
    parent=list(range(n)); size=[1]*n
    def find(x):
        while parent[x]!=x:
            parent[x]=parent[parent[x]]; x=parent[x]
        return x
    def union(a,b):
        ra,rb=find(a),find(b)
        if ra==rb: return False
        if size[ra]<size[rb]: ra,rb=rb,ra
        parent[rb]=ra; size[ra]+=size[rb]
        return True
    for a,b in edges: union(a,b)
    return find
qdata={}
for c in P:
    find=dsu(D,prev[c]); roots=sorted({find(x) for x in range(D)}); idx={rt:i for i,rt in enumerate(roots)}; comp=[idx[find(x)] for x in range(D)]
    qdata[c]=(comp,len(roots),comp[c])
    comps=collections.defaultdict(list)
    for x in range(D): comps[comp[x]].append(x)
    print('color',c,'prev_edges',prev[c],'components',dict(comps),'root_component',comp[c],'delta',((c+s)%D,p[(c+s)%D]))
def comp_edge(comp,e):
    a,b=e; ia,ib=comp[a],comp[b]
    return None if ia==ib else tuple(sorted((ia,ib)))
def support_ok(M):
    for c in P:
        comp,n,root=qdata[c]
        parent=list(range(n)); size=[1]*n; seen=set()
        def find(x):
            while parent[x]!=x:
                parent[x]=parent[parent[x]]; x=parent[x]
            return x
        def union(a,b):
            ra,rb=find(a),find(b)
            if ra==rb: return False
            if size[ra]<size[rb]: ra,rb=rb,ra
            parent[rb]=ra; size[ra]+=size[rb]
            return True
        for e in M:
            qe=comp_edge(comp,e)
            if qe is None or qe in seen: return False
            seen.add(qe)
            if not union(*qe): return False
        comps={}
        for i in range(n): comps.setdefault(find(i),[]).append(i)
        if sorted(len(v) for v in comps.values()) != [1,4]: return False
        big=[v for v in comps.values() if len(v)==4][0]
        if root not in big: return False
    return True
def lam(c,M,e,delta):
    comp,n,root=qdata[c]; se=comp_edge(comp,e)
    if se is None: return None
    adj=[set() for _ in range(n)]; rem=False
    for x,y in M:
        qe=comp_edge(comp,(x,y))
        if qe is None: return None
        if qe==se and not rem:
            rem=True; continue
        adj[qe[0]].add(qe[1]); adj[qe[1]].add(qe[0])
    if not rem: return None
    seen={root}; stack=[root]
    while stack:
        u=stack.pop()
        for v in adj[u]:
            if v not in seen: seen.add(v); stack.append(v)
    desc=set(range(n))-seen
    t,h=delta
    return int(comp[h] in desc)-int(comp[t] in desc)
def det(v,w): return v[0]*w[1]-v[1]*w[0]
def active_ok(M):
    deltas={c:((c+s)%D,p[(c+s)%D]) for c in P}
    for e1,e2 in itertools.combinations(M,2):
        vecs=[]; good=True
        for c in P:
            vals={e:lam(c,M,e,deltas[c]) for e in M}
            if any(v!=0 for e,v in vals.items() if e not in (e1,e2)):
                good=False; break
            v=(vals[e1],vals[e2])
            if v==(0,0) or any(x not in (-1,0,1) for x in v):
                good=False; break
            vecs.append(v)
        if good and all(abs(det(vecs[i],vecs[j]))==1 for i in range(3) for j in range(i+1,3)):
            return (e1,e2,vecs)
    return None
all_edges=[(i,j) for i in range(D) for j in range(i+1,D)]
co=[]; act=[]
for M in itertools.combinations(all_edges,3):
    if support_ok(M):
        co.append(M)
        a=active_ok(M)
        if a: act.append((M,a))
print('total triples checked',7140)
print('simultaneous rooted coforest supports',len(co))
print('active A2 supports',len(act))
print('first coforest examples',co[:20])
# for coforest supports, count max number of colors with delta contained in span of some edge-pair?
failtypes=collections.Counter()
for M in co:
    best=0; bestdata=None
    deltas={c:((c+s)%D,p[(c+s)%D]) for c in P}
    for e1,e2 in itertools.combinations(M,2):
        ok_colors=0; vecs=[]
        for c in P:
            vals={e:lam(c,M,e,deltas[c]) for e in M}
            if all(v==0 for e,v in vals.items() if e not in (e1,e2)):
                ok_colors+=1; vecs.append((c,(vals[e1],vals[e2])))
        if ok_colors>best: best=ok_colors; bestdata=(e1,e2,vecs)
    failtypes[best]+=1
print('best colors whose delta lies in a common two-edge active plane:',dict(failtypes))
