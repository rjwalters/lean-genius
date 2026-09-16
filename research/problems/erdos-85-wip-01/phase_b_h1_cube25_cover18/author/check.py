"""Apply reviewed660clause cover template to18archived exact bases; no solver."""
from pathlib import Path
import hashlib,json,time
P=Path(__file__).parent;R=Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration/research/problems/erdos-85-wip-01');T=R/'phase_b_h1_cube25_cnf_cover/author/clause-certificate.json';B=R/'phase_b_h1_cube25_cover/binding-results.json'
sha=lambda b:hashlib.sha256(b).hexdigest()
def main():
 assert not (P/'launch.json').exists()
 traw=T.read_bytes();braw=B.read_bytes();template=json.loads(traw);bindings=json.loads(braw);rows=bindings['results'];assert len(rows)==18 and len({r['tag'] for r in rows})==18
 requirements={}
 for cert in template['certificates']:
  for i,c in enumerate(cert['counter_clauses'],cert['counter_start_clause']):assert i not in requirements;requirements[i]=c
  for item in cert['block_clauses']:assert item['index'] not in requirements;requirements[item['index']]=item['clause']
 assert len(requirements)==660
 launch={'seconds':60,'cases':18,'template_sha256':sha(traw),'bindings_sha256':sha(braw),'driver_sha256':sha(Path(__file__).read_bytes()),'criterion_review':2723,'scope':'Read-only exact clause containment, no solver/proof replay.'};(P/'launch.json').write_text(json.dumps(launch,indent=2)+'\n')
 start=time.monotonic();results=[]
 for row in rows:
  assert time.monotonic()-start<60
  raw=Path(row['cube_path']).read_bytes();assert sha(raw)==row['cube_sha256'];lines=raw.splitlines(keepends=True);head=lines[0].split();assert head[:2]==[b'p',b'cnf'];nv,nc=map(int,head[2:]);assert len(lines)==nc+1
  assert lines[-2:]==[b'301 0\n',b'456 0\n']
  base=f'p cnf {nv} {nc-2}\n'.encode()+b''.join(lines[1:-2]);assert sha(base)==row['frozen_base_sha256']
  for i,clause in requirements.items():
   assert 1<=i<=nc-2 and max(map(abs,clause))<=nv
   assert list(map(int,lines[i].split()))==clause+[0],(row['tag'],i)
  results.append({'tag':row['tag'],'cube_path':row['cube_path'],'cube_sha256':sha(raw),'base_sha256':sha(base),'base_variables':nv,'base_clauses':nc-2,'required_clauses_checked':660,'status':'PASS_SAME_REVIEWED_CLAUSE_TEMPLATE'})
 out={'status':'PASS18_EXACT_CNF_COVERS','results':results,'count':18,'required_occurrences':18*660,'seconds':time.monotonic()-start,'scope':'Accepted2723propositional cover transfers by identical clauses. No UNSAT/proof verification, fresh canonical identity or category admission claimed for new cases.'};(P/'results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='results'}))
if __name__=='__main__':main()
