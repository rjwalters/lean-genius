from pathlib import Path
import json,itertools
from incidence import enumerate_incidences
P=Path(__file__).parent;S=Path('/Users/rwalters/lean-genius-q7-outside-first-20260910/h7-a7-empty-first');data=json.loads((S/'results.json').read_text());Fcases=[{tuple(sorted((i,(i+1)%7))) for i in range(7)},{(0,1),(0,2),(1,2),(3,4),(3,5),(4,5),(5,6)}];rows=[]
for r in data['fixtures']:
 phi={tuple(e):x for e,x in r['phi']};F=Fcases[r['F_case']];actual=enumerate_incidences(phi,F);fg=[set() for _ in range(7)]
 for x,y in F:fg[x].add(y);fg[y].add(x)
 expected=[]
 for code_tuple in itertools.product(range(3),repeat=7):
  selected=[actual['pairs'][i][j] for i,j in enumerate(code_tuple)]
  if len(set(selected))==7 and all(not fg[x]&fg[y] for x,y in selected):expected.append(sum(j<<(2*i) for i,j in enumerate(code_tuple)))
 assert sorted(expected)==actual['solutions'] and len(expected)==r['c4_free_choices']
 rows.append({'R':r['R_case'],'F':r['F_case'],'solutions':len(expected),'nodes':actual['nodes']})
(P/'test-results.json').write_text(json.dumps({'status':'PASS','cases':rows,'scope':'Only four reviewed fixedcolouring fixtures; no complete-family incidence enumeration launched.'},indent=2)+'\n');print(rows)
