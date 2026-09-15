"""claude third-seat check of F14 S-P projection certificates: own bitmask implementation of the
2712/2713 family model (demand-1 pairs need a 3-edge matching on the 6 remaining high colours,
demand-3 pairs a 2-edge matching on 4), and an own replay of negative trees."""
import json,gzip,random,itertools,sys,collections,time
from pathlib import Path
P=Path('/Users/rwalters/lean-genius-h7-a6-f14-incidence-cover-sol2-20260915'); B=Path('/Users/rwalters/lean-genius-h7-a6-f14-sol1-20260915')
random.seed(20260915)
recs=[]
with gzip.open(P/'receipts-000.jsonl.gz','rt') as f:
    for line in f: recs.append(json.loads(line))
emp=[r for r in recs if r['certificate']['status']=='EMPTY_FAMILY']; inf=[r for r in recs if r['certificate']['status']=='INFEASIBLE_PROJECTION']
if sys.argv[1]=='all': NE,NI=len(emp),len(inf); sample=emp+inf
else:
    NE,NI=int(sys.argv[1]),int(sys.argv[2]); sample=random.sample(emp,NE)+random.sample(inf,NI)
want={r['global_index'] for r in sample}
base={}
with gzip.open(B/'inputs.jsonl.gz','rt') as f:
    for line in f:
        r=json.loads(line)
        if r['global_index'] in want: base[r['global_index']]=[sum(1<<v for v in ns) for ns in r['neighbors']]
hosts={}
H=json.load(open(B/'hosts/results.json'))
for s in H['shards']:
    with gzip.open(B/'hosts'/s,'rt') as f:
        for line in f:
            h=json.loads(line)
            if h['global_index'] in want: hosts[h['global_index']]=h['receipt']['solutions']
def graph(gid,j):
    g=base[gid][:]
    for e,m in enumerate(hosts[gid][j],42):
        g[e]|=m; mm=m
        while mm:
            b=mm&-mm; mm-=b; g[b.bit_length()-1]|=1<<e
    return g
HI=(1<<7)-1; SING=list(range(7,21)); PAIR=list(range(21,42))
def perfect_matching_exists(colours,edges):
    # colours: set of high labels; edges: set of frozenset pairs; own recursive check (max-element first)
    if not colours: return True
    c=max(colours)
    for e in edges:
        if c in e:
            o=next(x for x in e if x!=c)
            if o in colours and perfect_matching_exists(colours-{c,o},edges): return True
    return False
def families(g):
    hi=lambda u:g[u]&HI
    demand={u:7-2*bin(g[u]).count('1') for u in PAIR}   # pair vertex has 2 high + some empty neighbours; needs 7 total
    cap={v:7-bin(g[v]).count('1') for v in SING}
    assert set(demand.values())<={1,3} and set(cap.values())<={2,3} and sum(demand.values())==sum(cap.values())==39
    fam={}
    for u in PAIR:
        Nu=g[u]
        nb=[w for w in range(49) if Nu>>w&1]
        cand=[v for v in SING if all(not (g[v]&g[w]) for w in nb)]   # adding u~v: no common neighbour with u, and no common neighbour with any neighbour of u (else C4 u-w-x-v)
        out=[]
        for ch in itertools.combinations(cand,demand[u]):
            if any(g[a]&g[b] for a,b in itertools.combinations(ch,2)): continue   # two chosen singletons sharing a neighbour + u = C4
            used=0
            for v in ch: used|=hi(v)
            if bin(used).count('1')!=demand[u]: continue
            left={c for c in range(7) if not used>>c&1}
            forb=Nu
            for v in ch: forb|=g[v]
            forbn=nb+list(ch)
            edges={frozenset({c for c in range(7) if hi(w)>>c&1}) for w in PAIR if w!=u and (hi(w)&~used)==hi(w) and all(not (g[w]&g[x]) for x in forbn)}
            if perfect_matching_exists(left,edges): out.append(sum(1<<(v-7) for v in ch))
        fam[u]=out
    return fam,cap
t=time.time(); ok_e=bad_e=0; ok_i=bad_i=0; tree_ok=tree_bad=0; notes=collections.Counter()
for r in sample:
    c=r['certificate']; g=graph(r['global_index'],r['leaf_index']); fam,cap=families(g)
    if c['status']=='EMPTY_FAMILY':
        if fam[c['pair_vertex']]==[]: ok_e+=1
        else: bad_e+=1; notes['nonempty_cited']+=1
    else:
        mine={str(u):sorted(fam[u]) for u in PAIR}; theirs={k:sorted(v) for k,v in c['families'].items()}
        capm=[cap[v] for v in SING]
        if mine==theirs and capm==c['capacity']: ok_i+=1
        else:
            bad_i+=1; notes['family_or_cap_mismatch']+=1
            if bad_i<=2: print("MISMATCH gid",r['global_index'],"leaf",r['leaf_index'],[u for u in PAIR if mine[str(u)]!=theirs.get(str(u))][:5], capm==c['capacity'])
        # own tree replay: node = (depth, remaining cap, chosen family per assigned pair); accept branch structure if every non-child family is rejected by capacity or by pairwise common-neighbour>1
        order=c['order']; tree=c['tree']; nodes={i:n for i,n in enumerate(tree)}
        common={(u,w):bin(g[u]&g[w]).count('1') for u in PAIR for w in PAIR if u<w}
        def replay(idx,capleft,assigned):
            n=nodes[idx]; d=n['depth']; u=order[d]; kids={b['family']:b['child'] for b in n['branches'] if 'child' in b}; rejs={b['family']:b for b in n['branches'] if 'child' not in b}
            for fi,F in enumerate(c['families'][str(u)]):
                chosen=[7+i for i in range(14) if F>>i&1]
                rej_cap=any(capleft[v]<=0 for v in chosen)
                rej_c4=any(bin(F&Fw).count('1')+common[(min(u,w),max(u,w))]>1 for w,Fw in assigned.items())
                if fi in kids:
                    if rej_cap or rej_c4: notes['child_but_rejectable']+=1
                    cl=dict(capleft)
                    for v in chosen: cl[v]-=1
                    a=dict(assigned); a[u]=F
                    if not replay(kids[fi],cl,a): return False
                else:
                    if fi in rejs:
                        kind='capacity' if 'capacity_reject' in rejs[fi] else ('common' if 'common_neighbour_reject' in rejs[fi] else 'other')
                        notes['explicit_reject_'+kind]+=1
                        if (kind=='capacity' and not rej_cap) or (kind=='common' and not rej_c4): notes['stated_reason_not_reproduced']+=1; return False
                    else: notes['implicit_reject']+=1
                    if not (rej_cap or rej_c4): notes['unrejected_alternative']+=1; return False
            return True
        if replay(0,dict(cap),{}): tree_ok+=1
        else: tree_bad+=1
print(f"EMPTY_FAMILY sample {NE}: ok {ok_e} bad {bad_e} | INFEASIBLE sample {NI}: families+capacity equal {ok_i} mismatch {bad_i} | trees replayed ok {tree_ok} bad {tree_bad} | notes {dict(notes)} | {time.time()-t:.1f}s")
