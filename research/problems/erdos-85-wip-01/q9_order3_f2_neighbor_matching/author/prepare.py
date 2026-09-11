from pathlib import Path
import json,hashlib
p=Path(__file__).parent;ps=Path('/tmp/erdos85-sol1-q9-order3-f2-phase-cover/phase-parameters.json');ts=Path('/tmp/erdos85-sol1-q9-order3-f2-contingency/receipts.json');params=json.loads(ps.read_text());states=json.loads(ts.read_text());cache={}
with (p/'inputs.txt').open('w') as f:
 for index,(si,ti,voltage,*masks) in enumerate(params):
  r=states[si];key=(si,voltage)
  if key not in cache:
   es=[(1,2),(4,5)]+[(a,3+b) for a,b in enumerate(r['mapping']) if b>=0];parent=list(range(6));adj=[0]*18
   def find(i):
    while parent[i]!=i:i=parent[i]
    return i
   for a,b in es:
    x,y=find(a),find(b);shift=voltage if x==y else 0;parent[x]=y
    for g in range(3):u=3*a+g;v=3*b+(g+shift)%3;adj[u]|=1<<v;adj[v]|=1<<u
   cache[key]=adj
  word=[]
  for a in range(3):
   for b in range(3):
    for s in range(3):
     if masks[3*a+b]>>s&1:word.extend([3*a,3*b+s])
  if r['cross_orbits']==3:
   if r['missing_labels'] is None:word.extend([-1,-1])
   else:a,b=r['missing_labels'];word.extend([3*a,-1,-1,3*b])
  assert len(word)==40
  f.write(' '.join(map(str,[index,*cache[key],*word]))+'\n')
(p/'input-pins.json').write_text(json.dumps({str(q):hashlib.sha256(q.read_bytes()).hexdigest() for q in (ps,ts)},indent=2)+'\n')
print('Prepared',len(params),'phase inputs')
