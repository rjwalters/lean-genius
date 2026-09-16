"""Fresh canonical CNF identity only; no solver or proof checker is called."""
import hashlib,json,sys,time
from pathlib import Path
R=Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration');P=Path(__file__).parent
sys.path.insert(0,str(R/'research/problems/erdos-85-wip-01/sat49'))
import materialize_h1_verdict_input as m
read=lambda p:json.loads(p.read_text());sha=m.sha256
manifest=R/'research/problems/erdos-85-wip-01/phase_b_h1_h3/h1-frozen-candidates.json';candidate=Path('/Users/rwalters/lean-genius-cayley-sol2-20260915/h1-cube25-evidence/candidate.json');C=read(candidate)
for n,h in read(candidate.parent/'pins.json').items():assert sha(candidate.parent/n)==h
out=Path('/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/h1-identity-20260916/0bbee37fe45d9447');out.parent.mkdir(parents=True,exist_ok=True)
assert not out.exists() and not (P/'launch.json').exists()
launch={'case_id':C['id'],'emit_check_seconds_each':120,'aggregate_seconds':300,'solver_launched':False,'proof_replay_launched':False,'candidate_sha256':sha(candidate),'manifest_sha256':sha(manifest),'emitter_sha256':m.EMITTER_SHA256,'image_id':m.IMAGE_ID,'runner_sha256':sha(Path(m.__file__)),'validator_sha256':sha(Path(m.validator.__file__)),'driver_sha256':sha(Path(__file__)),'output_dir':str(out)}
(P/'launch.json').write_text(json.dumps(launch,indent=2)+'\n');start=time.monotonic()
result=m.materialize(manifest,launch['manifest_sha256'],C['id'],out,timeout=120,cancelled=lambda:time.monotonic()-start>=300)
assert time.monotonic()-start<300 and result['status']=='materialized' and result['container_absent']
assert result['cnf_sha256']==C['cubes'][0]['base_sha256']
(P/'receipt.json').write_text(json.dumps(result,indent=2)+'\n')
(P/'generation.json').write_text(json.dumps({'status':'FRESH_NATIVE_BASE_HASH_MATCH','seconds':time.monotonic()-start,'cnf_sha256':result['cnf_sha256'],'bytes':result['cnf_bytes'],'variables':result['variables'],'clauses':result['clauses'],'scope':'Fresh input identity only. All25archived cube joins are a separate audit; no proof verification or case exclusion.'},indent=2)+'\n')
print((P/'generation.json').read_text())
