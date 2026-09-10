import json,itertools,time,hashlib
from pathlib import Path
src=Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration/research/problems/erdos-85-wip-01/q7_h7_labelled_incidence/pilot-1.json');raw=src.read_bytes();run=json.loads(raw);deadline=time.monotonic()+60;out=[]
for rec in run['results']:
 if not rec['witness']:continue
 G=[set() for _ in range(49)]
 for u,v in rec['witness']['partial_edges']:G[u].add(v);G[v].add(u)
 V=list(range(14,49));S={v:sum(1<<c for c in G[v] if c<7) for v in V};nodes=0
 def dfs():
  global nodes
  nodes+=1
  if nodes>100000 or time.monotonic()>deadline:raise TimeoutError
  missing={}
  for v in V:
   covered=[c for w in G[v] if w in S for c in range(7) if S[w]>>c&1]
   assert len(covered)==len(set(covered))
   missing[v]=127-sum(1<<c for c in covered)
   n=7-len(G[v]);m=missing[v].bit_count()
   if n<0 or not n<=m<=2*n:return False
  active=[v for v in V if missing[v]]
  if not active:return True
  candidates={v:[w for w in V if w!=v and w not in G[v] and len(G[w])<7 and not S[w]&~missing[v] and not S[v]&~missing[w] and all(not G[w]&G[x] for x in G[v])] for v in active}
  v=min(active,key=lambda v:len(candidates[v]));need=7-len(G[v]);domains=[]
  def partitions(left,selected):
   if time.monotonic()>deadline:raise TimeoutError
   if not left:
    if len(selected)==need:domains.append(selected)
    return
   slots=need-len(selected)
   if not slots<=left.bit_count()<=2*slots:return
   bit=left&-left
   for w in candidates[v]:
    if S[w]&bit and not S[w]&~left and all(not G[w]&G[x] for x in selected):partitions(left^S[w],selected+[w])
  partitions(missing[v],[])
  for group in domains:
   for w in group:G[v].add(w);G[w].add(v)
   if dfs():return True
   for w in group:G[v].remove(w);G[w].remove(v)
  return False
 try:
  exists=dfs();status='UNEXPECTED_FULL_GRAPH' if exists else 'INDEPENDENTLY_EXHAUSTED'
 except TimeoutError:status='VERIFICATION_CAPPED'
 out.append(dict(mask=rec['mask'],status=status,nodes=nodes));print(out[-1],flush=True)
 if status!='INDEPENDENTLY_EXHAUSTED':break
Path('independent-results.json').write_text(json.dumps(dict(input_sha256=hashlib.sha256(raw).hexdigest(),results=out,scope='Fixed26 saved assignments only; whole-neighborhood branching, no search source imported'),indent=2)+'\n')
