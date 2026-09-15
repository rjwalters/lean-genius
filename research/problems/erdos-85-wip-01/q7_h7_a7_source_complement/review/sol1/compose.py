import collections,hashlib,json,sqlite3
from pathlib import Path
P=Path('/Users/rwalters/lean-genius-h7-a7-source-complement-sol2-20260915');O=Path(__file__).parent
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in read(P/'pins.json').items():assert sha(P/n)==h
for n,h in read(O/'launch.json')['inputs'].items():assert sha(Path(n))==h
m=read(P/'coverage-map.json');assert m['status']=='PASS_EXACT_SOURCE_PARTITION'
sources={}
for k,v in m['sources'].items():
    assert sha(Path(v['path']))==v['sha256'];sources[k]=read(Path(v['path']))['results']
assert len(m['rows'])==1310
used=set();shape=collections.defaultdict(lambda:collections.Counter())
for i,r in enumerate(m['rows']):
    assert r['source_index']==i and r['status']=='COMPLETE'
    origin='original2116' if i<860 else 'new-complement';assert r['origin']==origin
    src=sources[origin][r['record_index']]
    assert src['source_index']==i and src['F_index']==r['F_index'] and src['status']=='COMPLETE' and src['count']==r['saved_graphs']
    key=(origin,r['record_index']);assert key not in used;used.add(key)
    shape[r['F_index']]['bases']+=1;shape[r['F_index']]['graphs']+=src['count']
assert sum(x['graphs'] for x in shape.values())==74549
assert shape[10]=={'bases':48,'graphs':14996} and shape[11]=={'bases':301,'graphs':6601} and shape[13]=={'bases':133,'graphs':14124}
c=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True)
r=c.execute('select status,resolution from review_requests where id=2116').fetchone();assert r[0]=='resolved' and r[1].startswith('PASS')
a=read(O/'REVIEW.json');assert a['complete_union']==1310 and a['graphs_checked']==28837
out={'status':'PASS_REVIEW2683','complete_bases':1310,'graphs':74549,'shape_counts':dict(shape),'source_manifest_sha256':sha(P/'pins.json'),'independent_new_graph_seconds':a['seconds'],'scope':'Exact disjoint source composition and all new graph outputs verified. Enumeration completeness rests on unchanged accepted2116 traversal-code audit, not independent exhaustive S replay. No downstream high/host/root/kernel/global conclusion.'}
(O/'REVIEW2683.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
