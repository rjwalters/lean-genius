import json,hashlib,itertools
from pathlib import Path
p=Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration/research/problems/erdos-85-wip-01/phase_b_local_drat45')
inventory=json.loads((p/'inventory.json').read_text());audit=json.loads((p/'results.json').read_text());out=[]
for row in inventory['rows']:
 if not (row['all_25_input_names_present'] and row['all_25_proof_names_present']):continue
 tag=row['tag'];records=[r for r in audit['results'] if r['tag']==tag];pairs={tuple(r['removed_trailing_units']) for r in records};left=sorted({a for a,b in pairs});right=sorted({b for a,b in pairs});product=pairs==set(itertools.product(left,right)) and len(left)==len(right)==5
 first=records[0];path=Path(first['cube_path']);raw=path.read_bytes();assert hashlib.sha256(raw).hexdigest()==first['cube_sha256'];lines=raw.splitlines();hits={}
 # Exclude header and the two cube-specific unit clauses.
 for i,line in enumerate(lines[1:-2],1):
  tokens=line.split()
  if len(tokens)!=6:continue
  values=[int(t) for t in tokens];assert values[-1]==0
  for key,want in [('left',left),('right',right)]:
   if sorted(values[:-1])==want:hits.setdefault(key,i)
 result={'tag':tag,'historical_list_class':row['historical_list_class'],'left':left,'right':right,'pair_count':len(pairs),'is_full_5x5_product':product,'base_clause_indices':hits,'both_factor_clauses_present':len(hits)==2,'sample_cube_path':str(path),'sample_cube_sha256':first['cube_sha256'],'frozen_base_sha256':first['frozen_base_sha256']};out.append(result)
print(json.dumps({'cases':len(out),'products':sum(r['is_full_5x5_product'] for r in out),'both_base_clauses':sum(r['both_factor_clauses_present'] for r in out)},indent=2));Path(__file__).with_name('results.json').write_text(json.dumps({'results':out,'solver_launched':False,'proof_replayed':False,'scope':'Checks pair product and literal disjunctions present in the base. No DRAT validity or UNSAT claim.'},indent=2)+'\n')
