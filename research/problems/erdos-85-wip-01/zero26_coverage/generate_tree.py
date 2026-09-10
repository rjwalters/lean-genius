from pathlib import Path
import json,itertools,time,importlib.util
p=Path(__file__).parent
root=Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration')
spec=importlib.util.spec_from_file_location('u',root/'research/problems/erdos-85-wip-01/low_degree_obstructions/count.py');u=importlib.util.module_from_spec(spec);spec.loader.exec_module(u)
U=u.adjacency(24,24,(3, 1, 4, 0, 2),None);R=[0]*8
for a,b in [(0,1),(2,3),(6,0),(7,0)]:R[a]|=1<<b;R[b]|=1<<a
fixed=U+[x<<15 for x in R]+[0]
for j in range(6):fixed[23]|=1<<(15+j);fixed[15+j]|=1<<23
needR=[4-x.bit_count()-(j<6) for j,x in enumerate(R)]
def add(E,j,S):
 F=E.copy()
 for i in S:F[i]|=1<<(15+j);F[15+j]|=1<<i
 return F
def rectangle(E):
 for x,y in itertools.combinations(range(24),2):
  common=E[x]&E[y]
  if common.bit_count()>1:
   a=(common&-common).bit_length()-1;common&=common-1;b=(common&-common).bit_length()-1
   return [x,y,a,b]
 return None
candidates=[tuple(5*k+i for k,i in enumerate(t) if i>=0) for t in itertools.product(range(-1,5),repeat=3)]
domains=[[S for S in candidates if len(S)==needR[j] and rectangle(add(fixed,j,S)) is None] for j in range(8)]
assert list(map(len,domains))==[1,36,36,36,4,4,4,4]
lookup={}
start=time.monotonic();counts={'nodes':0,'leaf':0,'row':0,'rectangle':0,'order':0,'branch':0}
def visit(k,E):
 counts['nodes']+=1
 assert counts['nodes']<=1000000 and time.monotonic()-start<10,'bounded generation limit'
 for a,b in [(2,3),(4,5),(6,7)]:
  if a<k and b<k and (E[15+a]&32767)>(E[15+b]&32767):counts['order']+=1;return ['order',a,b]
 for i in range(15):
  d=E[i].bit_count()
  if d>4 or d+8-k<4:counts['row']+=1;return ['row',i]
 r=rectangle(E)
 if r:counts['rectangle']+=1;return ['rectangle',*r]
 if k==8:
  raise AssertionError('Unexpected leaf in zero-leaf proposal')
  row=tuple((E[i]>>15)&255 for i in range(15));assert row in lookup
  assert all(E[i].bit_count()==(6 if i==23 else 4) for i in range(24))
  counts['leaf']+=1;return ['leaf',lookup[row]]
 counts['branch']+=1
 return ['branch',[visit(k+1,add(E,k,S)) for S in domains[k]]]
subtrees=[]
for idx,S in enumerate(domains[1]):
 before=counts['nodes'];t=visit(2,add(add(fixed,0,domains[0][0]),1,S));subtrees.append({'index':idx,'nodes':counts['nodes']-before,'prefix_columns':[domains[0][0],S],'tree':t})
pilot=min((s for s in subtrees if s['nodes']>=500),key=lambda s:s['nodes'])
(p/'tree.json').write_text(json.dumps({'domains':domains,'counts':counts,'subtrees':subtrees,'elapsed_seconds':time.monotonic()-start,'scope':'Python explicit coverage-tree proposal only; no Lean coverage proved'},separators=(',',':'))+'\n')
(p/'pilot.json').write_text(json.dumps(pilot,separators=(',',':'))+'\n')
print(json.dumps({'counts':counts,'subtree_sizes':[s['nodes'] for s in subtrees],'pilot_index':pilot['index'],'pilot_nodes':pilot['nodes'],'elapsed_seconds':time.monotonic()-start}))
