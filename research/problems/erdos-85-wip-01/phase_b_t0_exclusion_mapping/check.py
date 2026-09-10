"""Read-only exact frozen H5/T0 case mapping; does not mutate a queue."""
from pathlib import Path
import json,hashlib,itertools
B=Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration/research/problems/erdos-85-wip-01');indexraw=(B/'phase_b_survivors_20260910.json').read_bytes();I=json.loads(indexraw);invpath=B/I['sources']['H5']['path'];invraw=invpath.read_bytes();assert hashlib.sha256(invraw).hexdigest()==I['sources']['H5']['sha256'];H=json.loads(invraw);base=H['bases']['h5_t0'];raw=Path(base['base']).read_bytes();assert hashlib.sha256(raw).hexdigest()==base['base_sha256'];lines=raw.splitlines(keepends=True);headers=[k for k,l in enumerate(lines) if l.lstrip().startswith(b'p cnf')];assert len(headers)==1;h=headers[0];assert list(map(int,lines[h].split()[2:]))==[29632,1328618]
maskaudit=json.loads((B/'q7_h5_t0_completion/lean-mask-bridge-audit.json').read_text());masks=maskaudit['masks'];clauses=[l for l in lines if l.strip() and not l.lstrip().startswith((b'c',b'p'))];prefix=clauses[:230]
actual={}
for line in prefix:
 t=list(map(int,line.split()));assert len(t)==2 and t[1]==0 and abs(t[0]) not in actual;actual[abs(t[0])]=t[0]
for k,(u,v) in enumerate(list(itertools.combinations(range(49),2))[:230],1):
 expected=k if (masks[v]>>u&1) else -k
 assert actual[k]==expected
assert set(actual)==set(range(1,231))
d=hashlib.sha256();size=0
for k,l in enumerate(lines):
 block=b'p cnf 29632 1328620\n' if k==h else l;d.update(block);size+=len(block)
rows=[];indexmap={r['id']:r for r in I['cases']};selected=[(k,r) for k,r in enumerate(H['jobs']) if r['cell']=='h5_t0'];assert len(selected)==43
for k,r in selected:
 assert len(r['units'])==2 and r['kind']=='cube'
 assert r['units']==[base['left'][r['left_index']],base['right'][r['right_index']]]
 suffix=''.join(f'{x} 0\n' for x in r['units']).encode();q=d.copy();q.update(suffix)
 assert q.hexdigest()==r['cnf_sha256'] and size+len(suffix)==r['cnf_bytes']
 x=indexmap[r['id']];assert x['sector']=='H5' and x['source_index']==k and x['cnf_sha256']==r['cnf_sha256']
 rows.append({'id':r['id'],'source_index':k,'units':r['units'],'cnf_sha256':q.hexdigest(),'cnf_bytes':size+len(suffix)})
assert {r['id'] for r in rows}=={r['id'] for r in I['cases'] if r['id'].startswith('h5_t0.')}
result={'status':'EXACT_INPUT_MAPPING_ONLY','index_sha256':hashlib.sha256(indexraw).hexdigest(),'h5_inventory_sha256':hashlib.sha256(invraw).hexdigest(),'base_path':base['base'],'base_sha256':hashlib.sha256(raw).hexdigest(),'fixed_support_unit_count':230,'mapped_count':43,'rows':rows,'scope':'Every mapped input is exact canonical T0 base plus two units. Reviewed finite graph exclusion pertains to this support sector; mapping alone is not a solver UNSAT receipt, Lean proof, decoder theorem, or permission to alter the frozen queue. No CNFs written.'}
Path(__file__).with_name('results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='rows'}))
