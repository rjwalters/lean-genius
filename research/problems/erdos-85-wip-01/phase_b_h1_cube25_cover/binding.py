"""Check the 18 recorded complete cube sets against actual H1 edge prefixes."""
from pathlib import Path
import json,sys,hashlib,itertools
root=Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration');base=root/'research/problems/erdos-85-wip-01';sys.path.insert(0,str(base/'sat49'));import verify_h1_sat_graph as decoder
p=base/'phase_b_local_drat45';inventory=json.loads((p/'inventory.json').read_text());audit=json.loads((p/'results.json').read_text());manifest_path=base/'phase_b_h1_h3/h1-frozen-candidates.json';raw=manifest_path.read_bytes();rows={r['tag']:r for r in json.loads(raw)['rows']};results=[]
for row in inventory['rows']:
 if not (row['all_25_input_names_present'] and row['all_25_proof_names_present']):continue
 tag=row['tag'];records=[r for r in audit['results'] if r['tag']==tag];pairs={tuple(r['removed_trailing_units']) for r in records};assert pairs==set(itertools.product(range(301,306),range(456,461)));assert all(r['base_matches'] for r in records)
 first=records[0];profile=int(rows[tag]['profile']);ids,sha,count=decoder.verify_prefix(Path(first['cube_path']),profile);assert sha==first['cube_sha256'];left=[ids[(4,v)] for v in range(10,15)];right=[ids[(9,v)] for v in range(15,20)];assert left==list(range(301,306)) and right==list(range(456,461))
 results.append({'tag':tag,'profile':profile,'prefix_clauses_checked':count,'cube_path':first['cube_path'],'cube_sha256':sha,'frozen_base_sha256':first['frozen_base_sha256'],'pairs':sorted([list(pair) for pair in pairs]),'left_edges':[[4,v] for v in range(10,15)],'right_edges':[[9,v] for v in range(15,20)]})
assert len(results)==18
out={'count':len(results),'manifest_sha256':hashlib.sha256(raw).hexdigest(),'decoder_sha256':hashlib.sha256(Path(decoder.__file__).read_bytes()).hexdigest(),'results':results,'proof_replayed':False,'solver_launched':False,'scope':'Recorded 25 cube units exhaust choices of neighbor4 in block2 and neighbor9 in block3. Actual prefix binds literal IDs. Existing graph constraints, not explicit base clauses, force these choices; graph-side theorem is separate. No cube UNSAT or DRAT validity asserted.'};Path(__file__).with_name('binding-results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'count':len(results),'actual_prefixes_verified':len(results),'profiles':sorted({r['profile'] for r in results})}))
