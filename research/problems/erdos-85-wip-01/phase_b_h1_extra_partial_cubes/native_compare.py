from pathlib import Path
import sys,json,concurrent.futures,hashlib
root=Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration');sys.path.insert(0,str(root/'research/problems/erdos-85-wip-01/sat49'));import materialize_h1_verdict_input as m
p=Path(__file__).parent;manifest=root/'research/problems/erdos-85-wip-01/phase_b_h1_h3/h1-frozen-candidates.json';digest=m.sha256(manifest);records=json.loads((p/'results.json').read_text())['results'];tags=sorted({r['tag'] for r in records});assert len(tags)==6

def compare(tag):
 rows=[r for r in records if r['tag']==tag];derived={r['derived_base_sha256'] for r in rows};assert len(derived)==1
 receipt=m.materialize(manifest,digest,'h1_'+tag,p/'native'/tag,timeout=120)
 cnf=Path(receipt['cnf_path']);matched=derived=={receipt['cnf_sha256']}
 out={'tag':tag,'retained_cubes':len(rows),'derived_hashes':sorted(derived),'native_receipt':receipt,'canonical_match':matched,'proof_replayed':False,'solver_launched':False}
 target=p/'native'/tag/'comparison.json';target.write_text(json.dumps(out,indent=2)+'\n')
 if matched:
  assert m.sha256(cnf)==receipt['cnf_sha256'];cnf.unlink();out['owned_input_removed_after_match']=True;target.write_text(json.dumps(out,indent=2)+'\n')
 return out

(p/'native').mkdir(exist_ok=False)
out=[]
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
 for r in pool.map(compare,tags):
  out.append(r);print(json.dumps({'tag':r['tag'],'canonical_match':r['canonical_match'],'retained_cubes':r['retained_cubes']}),flush=True)
  (p/'native-results.json').write_text(json.dumps({'results':out,'target':6,'completed':len(out),'scope':'Canonical input identity for partial historical cubes only; no full 25-cube availability or proof verification claim.'},indent=2)+'\n')
