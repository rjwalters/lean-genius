"""Direct matrix audit; no search implementation imported."""
import json,itertools,hashlib
from pathlib import Path
core=json.loads(Path('core-t0.json').read_text());run=json.loads(Path('singleton-t0.json').read_text());masks=core['masks'];caps=[4+sum(bool(m>>c&1) for m in masks if m.bit_count()==3) for c in range(5)];supports=masks+[1<<c for c in range(5) for _ in range(caps[c])];supports+=[0]*(44-len(supports))
checked=[]
for row in run['results']:
 if row['status']!='PARTIAL_WITNESS':continue
 bits=row['witness']['adjacency'];assert len(bits)==49
 graph=[{j for j in range(49) if b>>j&1} for b in bits]
 for i in range(49):
  assert i not in graph[i] and bits[i]>>49==0
  for j in range(49):assert (j in graph[i])==(i in graph[j])
 for v,mask in enumerate(supports,5):assert graph[v]&set(range(5))=={c for c in range(5) if mask>>c&1}
 assert all(len(graph[c])==8 and not graph[c]&set(range(5)) for c in range(5))
 for u,v in itertools.combinations(range(49),2):assert len(graph[u]&graph[v])<=1
 for v,mask in enumerate(supports,5):
  assert len(graph[v])<=7
  if mask:
   for c in range(5):assert len(graph[v]&graph[c])==1
  else:assert not graph[v]
 actual=sum(1<<i for i,(u,v) in enumerate(itertools.combinations(range(len(masks)),2)) if v+5 in graph[u+5]);assert actual==row['core']
 checked.append(dict(core=row['core'],nonempty_rows=sum(bool(m) for m in supports),edges=sum(map(len,graph))//2,adjacency_sha256=hashlib.sha256(json.dumps(bits,separators=(',',':')).encode()).hexdigest()))
result=dict(checked=checked,pilot_sha256=hashlib.sha256(Path('singleton-t0.json').read_bytes()).hexdigest(),scope='Positive partial witnesses only; does not independently validate negative/capped search results')
Path('singleton-witness-audit.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
