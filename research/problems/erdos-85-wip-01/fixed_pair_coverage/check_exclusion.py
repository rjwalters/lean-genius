#!/usr/bin/env python3
"""Compile the two final links against retained checked coverage/rejection builds."""
from pathlib import Path
import argparse,hashlib,json,os,re,shutil,subprocess,time
ap=argparse.ArgumentParser();ap.add_argument('--coverage-build',type=Path,required=True);ap.add_argument('--rejections-build',type=Path,required=True);ap.add_argument('--representatives-build',type=Path);ap.add_argument('--build-dir',type=Path,required=True);ap.add_argument('--timeout',type=int,default=180)
a=ap.parse_args();p=Path(__file__).resolve().parent;b=a.build_dir.resolve()
if b.exists() and any(b.iterdir()):ap.error('build directory must be empty')
assert a.timeout>0
assert (a.coverage_build/'CoverageAssembly.olean').is_file()
assert (a.rejections_build/'OrderedLeaves.olean').is_file()
m=json.loads((p/'EXCLUSION_MANIFEST.json').read_text())
for x in m['modules']:assert hashlib.sha256((p/(x['name']+'.lean')).read_bytes()).hexdigest()==x['sha256']
b.mkdir(parents=True,exist_ok=True)
paths=[b,a.coverage_build.resolve(),a.rejections_build.resolve()]
if a.representatives_build:paths.append(a.representatives_build.resolve())
e=os.environ.copy();e['LEAN_PATH']=os.pathsep.join(map(str,paths))+os.pathsep+e.get('LEAN_PATH','')
results=[]
for x in m['modules']:
 n=x['name'];s=b/(n+'.lean');shutil.copy2(p/s.name,s);start=time.monotonic()
 with (b/(n+'.log')).open('w') as f:
  try:r=subprocess.run(['lean','--root',str(b),'-o',str(b/(n+'.olean')),str(s)],env=e,stdout=f,stderr=subprocess.STDOUT,timeout=a.timeout);rc=r.returncode;timeout=False
  except subprocess.TimeoutExpired:rc=None;timeout=True
 log=(b/(n+'.log')).read_text();axs=re.findall(r'depends on axioms:\s*\[([^\]]*)\]',log)
 ok=rc==0 and not timeout and len(axs)==x['expected_exports'] and all({z.strip() for z in y.split(',') if z.strip()}<={'propext','Classical.choice','Quot.sound'} for y in axs) and hashlib.sha256(s.read_bytes()).hexdigest()==x['sha256']
 results.append({'module':n,'returncode':rc,'timeout':timeout,'elapsed_seconds':time.monotonic()-start,'verified':ok,'source_sha256':x['sha256']})
 (b/'RESULT.json').write_text(json.dumps({'status':'failed' if not ok else 'complete' if len(results)==len(m['modules']) else 'running','results':results},indent=2)+'\n')
 if not ok:raise SystemExit(1)
print('Fixed-pair exclusion kernelPASS; no broader theorem is asserted.')
