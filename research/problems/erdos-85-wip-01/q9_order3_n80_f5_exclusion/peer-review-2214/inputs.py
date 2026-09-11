from pathlib import Path
import json,hashlib
from base import independent
s=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/q9-order3-local-row-propagation');d=Path(__file__).resolve().parent
for f,h in json.loads((s/'pins.json').read_text()).items():assert hashlib.sha256((s/f).read_bytes()).hexdigest()==h
pin=json.loads((s/'dependency.json').read_text());assert hashlib.sha256(Path(pin['path']).read_bytes()).hexdigest()==pin['sha256']
m=independent(24538199);n=len(m['words']);assert n==118
bounds={}
for row,label in zip(m['A'],m['labels']):
 if label[0]=='neighbor_margin':
  _,i,u,a=label;bounds[i,u,a]=-row.get(i,0)
lines=[str(n)]
for i,w in enumerate(m['words']):
 b=[bounds[i,u,a] for u in range(5) for a in range(3)];adj=[]
 for x,y in m['edges']:
  if x==i:adj.append(y)
  elif y==i:adj.append(x)
 lines.append(' '.join(map(str,[*w,*b,len(adj),*adj])))
text='\n'.join(lines)+'\n';assert text==(s/'input.txt').read_text();(d/'input.txt').write_text(text)
(d/'inputs.json').write_text(json.dumps({'status':'PASS','words':n,'edges':len(m['edges']),'independent_input_exact_match':True},indent=2)+'\n');print('Independent matrix input exact match:118 words')
