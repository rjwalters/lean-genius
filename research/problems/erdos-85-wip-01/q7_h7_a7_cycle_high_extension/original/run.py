"""One guarded pass: E/S graphs -> high pairing -> distinct pair hosts."""
import collections, hashlib, itertools, json, pathlib, sqlite3, time
P=pathlib.Path(__file__).parent
SOURCE=pathlib.Path('/Users/rwalters/lean-genius-q7-outside-first-20260910/h7-a7-cycle-singleton-host-projection')
K=list(itertools.combinations(range(7),2)); KI={e:i for i,e in enumerate(K)}
class Limit(Exception): pass
def base(rep, edges, F):
    g=[set() for _ in range(21)]
    for u,v in F+edges:g[u].add(v);g[v].add(u)
    for s, hosts in enumerate(rep['singleton_hosts'],7):
        for e in hosts:g[s].add(e);g[e].add(s)
    return g
def full_graph(g, pairing, matchings):
    # H=0..6; double-E S=7..13; single-E S=14..20; P=21..41; E=42..48.
    out=[set() for _ in range(49)]
    def add(u,v):out[u].add(v);out[v].add(u)
    def ren(u):return u+42 if u<7 else u
    for u in range(21):
        for v in g[u]:
            if u<v:add(ren(u),ren(v))
    for i,d in enumerate(pairing):add(i,14+i);add(i,7+d)
    for j,(a,b) in enumerate(K):add(21+j,a);add(21+j,b)
    for e,m in enumerate(matchings):
        for j in range(21):
            if m>>j&1:add(42+e,21+j)
    return [sorted(s) for s in out]
def extend(g, deadline):
    nodes=0; pairings=[]; solutions=[]
    def tick():
        nonlocal nodes
        nodes+=1
        if nodes>100000 or time.monotonic()>deadline:raise Limit
    allowed=[[d for d in range(7) if 7+d not in g[14+i] and not g[7+d]&g[14+i]] for i in range(7)]
    def hosts(pairing):
        colour={14+i:i for i in range(7)};colour.update({7+d:i for i,d in enumerate(pairing)})
        opts=[]
        for e in range(7):
            present=[colour[s] for s in g[e] if s>=7]
            assert len(present)==len(set(present))==3
            a,b,c,d=sorted(set(range(7))-set(present))
            opts.append([sum(1<<KI[tuple(sorted(z))] for z in matching) for matching in [((a,b),(c,d)),((a,c),(b,d)),((a,d),(b,c))]])
        def dfs(e,used,chosen):
            tick()
            if e==7:solutions.append([list(pairing),list(chosen)]);return
            for m in opts[e]:
                if not used&m:dfs(e+1,used|m,chosen+[m])
        dfs(0,0,[])
    def pair(i,used,p):
        tick()
        if i==7:pairings.append(list(p));hosts(p);return
        for d in allowed[i]:
            if not used>>d&1:pair(i+1,used|1<<d,p+[d])
    status='COMPLETE'
    try:pair(0,0,[])
    except Limit:status='UNKNOWN'
    return dict(status=status,nodes=nodes,allowed=allowed,pairings=pairings,solutions=solutions)
def main():
    assert not (P/'results.json').exists(), 'Never overwrite/retry a research pass'
    db=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True);db.row_factory=sqlite3.Row
    reviews=[]
    for i in [2096,2107]:
        row=dict(db.execute('select * from review_requests where id=?',(i,)).fetchone())
        assert row['status']=='resolved' and row['resolution'].startswith('PASS'),row
        reviews.append(row)
    (P/'premises.json').write_text(json.dumps(reviews,indent=2)+'\n')
    pins=json.loads((SOURCE/'pins.json').read_text())
    for f,h in pins.items():assert hashlib.sha256((SOURCE/f).read_bytes()).hexdigest()==h
    for f in ['results.json','completion-results.json','pins.json']:(P/('source-'+f)).write_bytes((SOURCE/f).read_bytes())
    reps=json.loads((P/'source-results.json').read_text());comp=json.loads((P/'source-completion-results.json').read_text())
    assert len(reps['representatives'])==202 and len(comp['results'])==202
    assert all(r['status']=='COMPLETE' for r in comp['results'])
    cases=[(r['source_index'],j,edges) for r in comp['results'] for j,edges in enumerate(r['solutions'])]
    assert len(cases)==459
    start=time.monotonic();deadline=start+60;results=[]
    for x,j,edges in cases:
        if time.monotonic()>deadline:break
        g=base(reps['representatives'][x],edges,reps['F_edges'])
        assert all(len(g[u]&g[v])<=1 for u in range(21) for v in range(u))
        r=extend(g,deadline);r.update(source_index=x,singleton_index=j);results.append(r)
    summary=dict(total=459,visited=len(results),unvisited=459-len(results),counts=dict(collections.Counter(r['status'] for r in results)),pairings=sum(len(r['pairings']) for r in results),solutions=sum(len(r['solutions']) for r in results),nodes=sum(r['nodes'] for r in results),seconds=time.monotonic()-start)
    (P/'results.json').write_text(json.dumps(dict(summary=summary,results=results),separators=(',',':'))+'\n');print(summary)
if __name__=='__main__':main()
