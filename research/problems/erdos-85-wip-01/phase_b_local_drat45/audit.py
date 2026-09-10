"""Read cube CNFs, remove exactly their two trailing units, compare frozen base hash."""
from pathlib import Path
import json,hashlib,re,time
base=Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration/research/problems/erdos-85-wip-01')
manifest=base/'phase_b_h1_h3/h1-frozen-candidates.json';raw=manifest.read_bytes();rows={r['tag']:r for r in json.loads(raw)['rows']}
dirs=json.loads(Path('/tmp/erdos85-sol1-local-drat45-cube-dirs.json').read_text());results=[];started=time.monotonic()
for directory in dirs:
 tag=directory['tag'];hashes={v for k,v in rows[tag].items() if k.endswith('cnf_sha256') and v};assert len(hashes)==1;expected=next(iter(hashes))
 for name in directory['cnfs']:
  path=Path(directory['path'])/name;data=path.read_bytes();head,body=data.split(b'\n',1);fields=head.split();assert len(fields)==4 and fields[:2]==[b'p',b'cnf'];n,m=map(int,fields[2:]);tail=body.rsplit(b'\n',3);assert len(tail)==4 and tail[-1]==b'';assert all(re.fullmatch(rb'-?[1-9][0-9]* 0',u) for u in tail[1:3]);units=[int(u.split()[0]) for u in tail[1:3]];assert all(abs(u)<=n for u in units)
  h=hashlib.sha256(f'p cnf {n} {m-2}\n'.encode());h.update(tail[0]);h.update(b'\n');derived=h.hexdigest()
  results.append({'tag':tag,'cube_path':str(path),'cube_sha256':hashlib.sha256(data).hexdigest(),'cube_bytes':len(data),'variables':n,'clauses':m,'removed_trailing_units':units,'derived_base_sha256':derived,'frozen_base_sha256':expected,'base_matches':derived==expected})
 print(json.dumps({'tag':tag,'directory':directory['path'],'cubes':len(directory['cnfs'])}),flush=True)
out={'manifest_sha256':hashlib.sha256(raw).hexdigest(),'directories':len(dirs),'cube_inputs':len(results),'matching_base_inputs':sum(r['base_matches'] for r in results),'mismatch_inputs':sum(not r['base_matches'] for r in results),'seconds':time.monotonic()-started,'results':results,'proof_replayed':False,'solver_launched':False,'scope':'Byte reconstruction of root CNF by removing exactly two final unit clauses and decrementing header count. A base match binds the retained cube input to frozen base plus those units. It does not verify proof bytes, solve any cube, prove cube cover, or establish full-case closure.'};Path(__file__).with_name('results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='results'}))
