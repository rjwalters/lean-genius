import gzip,hashlib,json,pathlib,time
P=pathlib.Path(__file__).parent;A=pathlib.Path('/tmp/erdos85-sol1-h7-a6-projection-extension');Q=pathlib.Path('/tmp/erdos85-sol1-h7-a6-high-quotient')
def graphs():
 cover=json.loads((A/'source-cover-results.json').read_text());comp=json.loads((A/'source-completion-results.json').read_text())
 high={}
 with gzip.open(A/'high-colourings.jsonl.gz','rt') as f:
  for line in f:
   r=json.loads(line);high[r['completion_index'],r['singleton_index']]=r['colourings']
 reps=json.loads((Q/'representatives.json').read_text());selected=[r for r in reps if comp['results'][r['completion_index']]['F_index']==15];assert len(selected)==4536
 cache={}
 for r in selected:
  ci,j=r['completion_index'],r['singleton_index'];src=comp['results'][ci];c=high[ci,j][r['colouring_index']]
  if (ci,j) not in cache:
   F=cover['cases'][15];X=F['representatives'][src['X_index']];g=[set() for _ in range(49)]
   def ren(u):return u+42 if u<7 else u
   def add(a,b):g[a].add(b);g[b].add(a)
   for a,b in F['F_edges']+src['solutions'][j]:add(ren(a),ren(b))
   for s,hosts in enumerate(X['singleton_hosts'],7):
    for e in hosts:add(s,42+e)
   k=21
   for a in range(7):
    for b in range(a+1,7):add(k,a);add(k,b);k+=1
   cache[ci,j]=g
  g=[set(ns) for ns in cache[ci,j]]
  for d,h in enumerate(c):g[h].add(7+d);g[7+d].add(h)
  for h in range(3):g[h].add(18+h);g[18+h].add(h)
  yield dict(global_index=r['global_index'],completion_index=ci,singleton_index=j,colouring_index=r['colouring_index'],neighbors=[sorted(ns) for ns in g])
def main():
 assert not (P/'inputs.jsonl.gz').exists(),'Do not overwrite prepared input'
 start=time.monotonic();count=0;ids=[]
 with gzip.open(P/'inputs.jsonl.gz','wt') as f:
  for r in graphs():
   g=[set(ns) for ns in r['neighbors']];assert all(len(g[h])==8 and not g[h]&set(range(7)) for h in range(7))
   assert all(len(g[p])==2 and g[p]<=set(range(7)) for p in range(21,42))
   gm=[sum(1<<v for v in ns) for ns in g]
   assert all((gm[a]&gm[b]).bit_count()<=1 for a in range(49) for b in range(a))
   assert all(len(g[s])==(4 if s<18 else 5) for s in range(7,21))
   assert all(len(g[e])==7-len(g[e]&set(range(42,49))) for e in range(42,49))
   f.write(json.dumps(r,separators=(',',':'))+'\n');count+=1;ids.append(r['global_index']);assert time.monotonic()-start<60
 assert count==len(set(ids))==4536
 out=dict(status='PASS',graphs=count,seconds=time.monotonic()-start,global_indices=ids)
 (P/'input-verification.json').write_text(json.dumps(out,separators=(',',':'))+'\n');print({k:v for k,v in out.items() if k!='global_indices'})
if __name__=='__main__':main()
