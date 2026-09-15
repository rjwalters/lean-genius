"""Materialize only the accepted a6 F17 high quotient; no new enumeration."""
import gzip,hashlib,itertools,json,sqlite3,time
from pathlib import Path
P=Path(__file__).parent
R=Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration/research/problems/erdos-85-wip-01')
A=R/'q7_h7_a6_high_pairing_cover/original';Q=R/'q7_h7_a6_high_quotient/original'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def load():
 for root in [A,Q]:
  for n,h in json.loads((root/'pins.json').read_text()).items():assert sha(root/n)==h
 cover=json.loads((A/'source-cover-results.json').read_text());comp=json.loads((A/'source-completion-results.json').read_text())
 high={}
 for line in gzip.open(A/'high-colourings.jsonl.gz','rt'):
  r=json.loads(line)
  if r['F_index']==17:
   assert r['status']=='COMPLETE';high[r['completion_index'],r['singleton_index']]=r['colourings']
 reps=[r for r in json.loads((Q/'representatives.json').read_text()) if comp['results'][r['completion_index']]['F_index']==17]
 assert len(reps)==77813 and sum(r['orbit_size'] for r in reps)==82817==sum(map(len,high.values()))
 assert len(high)==205 and len([r for r in comp['results'] if r['F_index']==17])==47
 return cover,comp,high,reps

def graph(cover,comp,high,r):
 ci,j=r['completion_index'],r['singleton_index'];src=comp['results'][ci]
 assert src['F_index']==17 and src['status']=='COMPLETE'
 F=cover['cases'][17];X=F['representatives'][src['X_index']];c=high[ci,j][r['colouring_index']]
 g=[set() for _ in range(49)]
 def ren(v):return v+42 if v<7 else v
 def add(u,v):g[u].add(v);g[v].add(u)
 for u,v in F['F_edges']+src['solutions'][j]:add(ren(u),ren(v))
 for s,hs in enumerate(X['singleton_hosts'],7):
  for e in hs:add(s,42+e)
 for p,hs in enumerate(itertools.combinations(range(7),2),21):
  for h in hs:add(p,h)
 for s,h in enumerate(c,7):add(s,h)
 for h in range(3):add(18+h,h)
 return g

def main():
 assert not (P/'inputs-launch.json').exists()
 db=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True);reviews={}
 for rid in [2118,2122,2125]:
  st,res=db.execute('select status,resolution from review_requests where id=?',(rid,)).fetchone();assert st=='resolved' and res.startswith('PASS');reviews[rid]=res
 cover,comp,high,reps=load()
 with (P/'inputs-launch.json').open('x') as f:json.dump({'total':77813,'raw_high_assignments':82817,'aggregate_seconds':60,'source_path':str(A),'quotient_path':str(Q),'source_pins_sha256':sha(A/'pins.json'),'quotient_pins_sha256':sha(Q/'pins.json'),'driver_sha256':sha(Path(__file__)),'reviews':reviews},f,indent=2)
 start=time.monotonic();seen=[]
 with gzip.open(P/'inputs.jsonl.gz','xt') as out:
  for r in reps:
   assert time.monotonic()-start<60
   g=graph(cover,comp,high,r);gm=[sum(1<<v for v in ns) for ns in g]
   assert all(len(g[h])==8 and not g[h]&set(range(7)) for h in range(7))
   assert all(len(g[p])==2 and g[p]<=set(range(7)) for p in range(21,42))
   assert all(u not in g[u] and all(u in g[v] for v in g[u]) for u in range(49))
   assert all((gm[u]&gm[v]).bit_count()<=1 for u in range(49) for v in range(u))
   assert all(len(g[s])==(4 if s<18 else 5) for s in range(7,21))
   assert all(len(g[e])==7-len(g[e]&set(range(42,49))) for e in range(42,49))
   record={k:r[k] for k in ['global_index','completion_index','singleton_index','colouring_index']};record['neighbors']=[sorted(ns) for ns in g]
   out.write(json.dumps(record,separators=(',',':'))+'\n');seen.append(r['global_index'])
 assert len(seen)==len(set(seen))==77813
 result={'status':'PASS_MATERIALIZED_INPUTS','graphs':len(seen),'raw_high_assignments':82817,'source_classes':47,'es_graphs':205,'global_indices':seen,'seconds':time.monotonic()-start,'input_sha256':sha(P/'inputs.jsonl.gz'),'scope':'Exact accepted high-quotient input slice only; no host or residual exclusion.'}
 (P/'input-verification.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='global_indices'}))
if __name__=='__main__':main()
