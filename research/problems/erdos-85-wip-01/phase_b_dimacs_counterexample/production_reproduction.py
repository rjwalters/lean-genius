import json,subprocess,time,importlib.util,hashlib
from pathlib import Path
p=Path('/tmp/erdos85-sol1-phase-b-inventory');out=Path('/tmp/erdos85-sol1-dimacs-review');original=p/'native-pilot.cnf';mutated=p/'native-pilot-framing-counterexample.cnf'
with original.open('rb') as s,mutated.open('wb') as d:
 d.write(next(s));first=next(s);second=next(s);assert first.endswith(b' 0\n') and second.endswith(b' 0\n')
 d.write(first[:-3]+b'\n');d.write(second[:-1]+b' 0\n')
 for b in iter(lambda:s.read(1048576),b''):d.write(b)
cmd=json.loads((p/'native-check-receipt.json').read_text())['command'];cmd[cmd.index('--name')+1]='erdos85-sol1-framing-counterexample';cmd[-1]='/inputs/'+mutated.name
t=time.monotonic()
try:r=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True,timeout=30)
except subprocess.TimeoutExpired:
 subprocess.run(['docker','rm','-f','erdos85-sol1-framing-counterexample'],capture_output=True);raise
receipt={'command':cmd,'rc':r.returncode,'stdout':r.stdout,'stderr':r.stderr,'seconds':time.monotonic()-t,'mutated_sha256':hashlib.sha256(mutated.read_bytes()).hexdigest(),'original_sha256':hashlib.sha256(original.read_bytes()).hexdigest(),'injected_empty_clause':True}
(out/'production-reproduction.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
