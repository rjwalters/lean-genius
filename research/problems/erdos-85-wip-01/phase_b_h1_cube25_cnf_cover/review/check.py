"""Declarative clause-schema check against fresh base, without producer decoder."""
import collections,hashlib,itertools,json,time
from pathlib import Path
P=Path(__file__).parent;A=Path('/Users/rwalters/lean-genius-h1-cube25-cnf-audit-sol2-20260916');N=Path('/Users/rwalters/lean-genius-h1-cube25-native-identity-sol1-20260916')
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
start=time.monotonic()
for n,h in read(A/'final-pins.json').items():assert sha(A/n)==h
cert=read(A/'clause-certificate.json');receipt=read(N/'receipt.json');base=Path(receipt['cnf_path']);assert sha(base)==cert['base_sha256']==receipt['cnf_sha256'];assert sha(Path(cert['cube_path']))==cert['cube_sha256']
requests={};targets=[]
for row in cert['certificates']:
 inputs=row['edge_ids'];grid=row['auxiliary_grid'];assert len(inputs)==len(set(inputs))==30 and all(0<v<=780 for v in inputs)
 assert len(grid)==24 and all(len(r)==6 for r in grid);aux=[v for r in grid for v in r];assert len(set(aux))==144 and all(780<v<=cert['base_variables'] for v in aux)
 # Declarative clauses, grouped by logical role rather than generator allocation order.
 expected=[(inputs[j],grid[0][j]) for j in range(6)]
 expected += [(-grid[k][j],grid[k][j+1]) for k in range(24) for j in range(5)]
 expected += [(inputs[j+k+1],-grid[k][j],grid[k+1][j]) for k in range(23) for j in range(6)]
 expected += [(inputs[j+24],-grid[23][j]) for j in range(6)]
 assert len(expected)==270 and collections.Counter(expected)==collections.Counter(map(tuple,row['counter_clauses']))
 for i,clause in enumerate(row['counter_clauses'],row['counter_start_clause']):
  assert i<=cert['base_clause_count'];requests.setdefault(i,set()).add(tuple(clause))
 # Only a partition of literal IDs is needed: no graph decoder is imported.
 groups=collections.defaultdict(list)
 for vertex,literal in zip(row['far_vertices'],inputs,strict=True):groups[vertex//5].append(literal)
 assert len(groups)==6 and all(len(g)==5 for g in groups.values())
 expected_blocks={(-a,-b) for g in groups.values() for a,b in itertools.combinations(g,2)}
 assert len(expected_blocks)==60 and expected_blocks=={tuple(x['clause']) for x in row['block_clauses']}
 for x in row['block_clauses']:
  assert 1<=x['index']<=cert['base_clause_count'];requests.setdefault(x['index'],set()).add(tuple(x['clause']))
 assert row['target_literals']==groups[row['target_block']];targets.append(row['target_literals'])
assert targets==[list(range(301,306)),list(range(456,461))]
seen=set();count=0
with base.open() as f:
 assert f.readline().split()==['p','cnf','42188','613280']
 for i,line in enumerate(f,1):
  count+=1
  if i in requests:
   xs=list(map(int,line.split()));assert xs[-1]==0 and requests[i]=={tuple(xs[:-1])};seen.add(i)
  assert time.monotonic()-start<60
assert count==cert['base_clause_count']==613280 and seen==set(requests)
assert len(cert['certificates'])==2 and sum(len(x['counter_clauses'])+len(x['block_clauses']) for x in cert['certificates'])==660
assert sha(base)==receipt['cnf_sha256']
out={'status':'PASS_INDEPENDENT_DECLARATIVE_CNF_COVER_CLAUSES','base_sha256':receipt['cnf_sha256'],'required_occurrences':660,'distinct_positions':len(seen),'target_literals':targets,'seconds':time.monotonic()-start,'author_manifest_sha256':sha(A/'final-pins.json'),'scope':'Exact necessary clause schemas checked in fresh native base. Semantic arbitrary-valuation proof reviewed separately; no UNSAT or proof replay.'}
(P/'REVIEW.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
