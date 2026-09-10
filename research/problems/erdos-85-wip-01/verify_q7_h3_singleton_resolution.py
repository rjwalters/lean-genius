"""Exact singleton resolution obstruction for two fixed induced H3 triple graphs.
No triangle-count assumption, optimization, timeout, or external inputs.
"""
from itertools import combinations,product
from pathlib import Path
import json
FIXTURES = {'5': [[0, 2], [0, 5], [0, 10], [0, 19], [1, 4], [1, 6], [1, 11], [1, 15], [2, 7], [2, 12], [2, 20], [3, 8], [3, 13], [3, 18], [3, 22], [4, 9], [4, 14], [4, 21], [5, 9], [5, 15], [5, 22], [6, 8], [6, 10], [6, 17], [7, 11], [7, 16], [7, 21], [8, 12], [8, 19], [9, 13], [9, 20], [10, 17], [10, 21], [11, 13], [11, 19], [12, 14], [12, 20], [13, 18], [14, 16], [14, 22], [15, 16], [15, 23], [16, 23], [17, 22], [17, 23], [18, 21], [18, 23], [19, 23], [20, 23]], '58': [[0, 1], [0, 5], [0, 10], [0, 15], [1, 6], [1, 11], [1, 20], [2, 3], [2, 7], [2, 12], [2, 18], [3, 8], [3, 13], [3, 19], [4, 9], [4, 14], [4, 21], [4, 22], [5, 8], [5, 15], [5, 22], [6, 12], [6, 17], [6, 21], [7, 9], [7, 11], [7, 16], [8, 14], [8, 19], [9, 13], [9, 20], [10, 13], [10, 18], [10, 21], [11, 19], [11, 22], [12, 14], [12, 17], [13, 20], [14, 16], [15, 16], [15, 23], [16, 23], [17, 22], [17, 23], [18, 21], [18, 23], [19, 23], [20, 23]]}

results=[]
for name,edges in FIXTURES.items():
 adj=[set() for _ in range(28)]
 assert len(edges)==49 and len(set(map(tuple,edges)))==49
 for u,v in edges:adj[u].add(v);adj[v].add(u)
 assert sorted(map(len,adj[:24]))==[4]*23+[6]
 assert adj[23]==set(range(15,21))
 for u,v in [(24,23)]+[(24,25+k) for k in range(3)]+[(25+k,5*k+i) for k in range(3) for i in range(5)]:adj[u].add(v);adj[v].add(u)
 assert all(len(adj[u]&adj[v])<=1 for u,v in combinations(range(28),2))
 covers=[];counts=[]
 for color in range(3):
  eligible=set(range(23))-set(range(5*color,5*color+5))
  assert len(eligible)==18
  triples=[t for t in combinations(sorted(eligible),3) if all(not(adj[u]&adj[v]) for u,v in combinations(t,2))]
  # Common special singleton neighbors automatically forbid two vertices in a Ui.
  assert all(all(sum(5*k<=v<5*k+5 for v in t)<=1 for k in range(3)) for t in triples)
  cs=[]
  def visit(left,chosen):
   if not left:
    assert len(chosen)==6
    cs.append(chosen);return
   opts=min(([t for t in triples if v in t and set(t)<=left] for v in left),key=len)
   for t in opts:visit(left-set(t),chosen+[t])
  visit(eligible,[]);counts.append(len(triples));covers.append(cs)
 pairsets=[[set(e for t in c for e in combinations(t,2)) for c in cs] for cs in covers]
 compatible=[(i,j,k) for i,x in enumerate(pairsets[0]) for j,y in enumerate(pairsets[1]) for k,z in enumerate(pairsets[2]) if not(x&y or x&z or y&z)]
 expected=[2,4,1] if name=='5' else [4,3,4]
 assert list(map(len,covers))==expected
 assert not compatible
 results.append({'fixture':name,'edges':edges,'candidate_triple_counts':counts,'individual_cover_counts':list(map(len,covers)),'compatible_joint_covers':len(compatible)})
Path(__file__).with_name('q7_h3_singleton_resolution.json').write_text(json.dumps({'scope':'Two fixed induced graphs cannot extend to the H3 triple profile at any triangle count','results':results},indent=2)+'\n')
print('PASS two fixed induced graphs excluded by joint singleton resolution; no whole profile exclusion')
