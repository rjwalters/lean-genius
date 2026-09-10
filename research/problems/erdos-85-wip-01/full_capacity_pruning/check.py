"""Run from repository proofs under lake env, with verified prerequisite builds."""
from pathlib import Path
import argparse,hashlib,json,os,re,subprocess,time
parser=argparse.ArgumentParser()
parser.add_argument('--dependency-build',action='append',type=Path,required=True)
parser.add_argument('--build-dir',type=Path,required=True)
parser.add_argument('--timeout',type=int,default=180)
a=parser.parse_args();assert a.timeout>0
p=Path(__file__).resolve().parent;b=a.build_dir.resolve()
if b.exists() and any(b.iterdir()):parser.error('Build directory must be empty; retained evidence must not be overwritten')
deps=[d.resolve() for d in a.dependency_build]
for d in deps:assert d.is_dir(),d
for n in ['TerminalReduction','SubsetCapacityBatch','Zero32Exclusion']:
 assert any((d/(n+'.olean')).is_file() for d in deps),n+' requires a verified prerequisite build'
s=p/'CapacityReduction.lean';expected='be324322294737ef5b069f9a8016c74c0b6a83c0bc1992001787beb159c74c9d'
assert hashlib.sha256(s.read_bytes()).hexdigest()==expected
b.mkdir(parents=True,exist_ok=True);src=b/s.name;src.write_bytes(s.read_bytes())
e=os.environ.copy();e['LEAN_PATH']=os.pathsep.join([str(b),*(str(d) for d in deps),e.get('LEAN_PATH','')])
t=time.monotonic()
with (b/'compile.log').open('w') as log:
 try:r=subprocess.run(['lean','--root='+str(b),'-o',str(src.with_suffix('.olean')),str(src)],env=e,stdout=log,stderr=subprocess.STDOUT,timeout=a.timeout);rc=r.returncode;timeout=False
 except subprocess.TimeoutExpired:rc=None;timeout=True
text=(b/'compile.log').read_text();axioms=re.findall(r'depends on axioms:\s*\[([^\]]*)\]',text)
count=len(axioms)+text.count('does not depend on any axioms')
axok=all({v.strip() for v in row.split(',') if v.strip()}<={'propext','Classical.choice','Quot.sound'} for row in axioms)
unchanged=hashlib.sha256(src.read_bytes()).hexdigest()==expected
ok=rc==0 and not timeout and count==7 and axok and unchanged and src.with_suffix('.olean').is_file()
result=dict(returncode=rc,timeout=timeout,seconds=time.monotonic()-t,exports=count,standard_axioms_only=axok,source_sha256=expected,source_unchanged=unchanged,verified=ok,dependency_builds=[str(d) for d in deps])
(b/'run.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)
raise SystemExit(0 if ok else 1)
