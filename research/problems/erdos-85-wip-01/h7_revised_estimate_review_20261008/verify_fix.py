"""Transport pinned sources; verify both estimate pairs on the existing builder."""
import base64
import hashlib
import json
from pathlib import Path
import shlex
import subprocess

ROOT = Path(__file__).resolve().parent
COMMIT = 'c95a89eced3ac79a66d369e988dee86f78c61715'
PKG = 'research/problems/erdos-85-wip-01/h7_hsb_campaign_20261008/'
FILES = ['estimate.py', 'README.md', 'receipts/inputs.json', 'receipts/sample_results.jsonl',
         'receipts/sample_results_with_followup.jsonl', 'receipts/estimate.json',
         'receipts/estimate_table.md', 'receipts/estimate_capped_at_1h.json',
         'receipts/estimate_table_capped_at_1h.md']
REMOTE = '''
import hashlib,json,pathlib,subprocess,sys,tempfile
b=json.load(sys.stdin)
assert pathlib.Path('/opt/e85/jobs').is_dir()
results=[]
with tempfile.TemporaryDirectory(prefix='h7-estimate-fix-') as d:
 p=pathlib.Path(d)
 for n,s in b['files'].items():
  assert hashlib.sha256(s.encode()).hexdigest()==b['sha256'][n]
  f=p/n;f.parent.mkdir(parents=True,exist_ok=True);f.write_text(s)
 for tag,sample,outj,outm in [
  ('revised','sample_results_with_followup.jsonl','estimate.json','estimate_table.md'),
  ('original','sample_results.jsonl','estimate_capped_at_1h.json','estimate_table_capped_at_1h.md')]:
  command=[sys.executable,'-B',str(p/'estimate.py'),'--inputs-json',str(p/'receipts/inputs.json'),
    '--sample',str(p/'receipts'/sample),'--json',str(p/'result.json'),'--md',str(p/'result.md')]
  r=subprocess.run(command,capture_output=True,text=True)
  assert r.returncode==0,r.stderr
  matches={}
  for actual,expected in [('result.json',outj),('result.md',outm)]:
   data=(p/actual).read_bytes();target=(p/'receipts'/expected).read_bytes()
   assert data==target,(tag,expected,'not byte-identical')
   matches[expected]=hashlib.sha256(data).hexdigest()
  result=json.loads((p/'result.json').read_text())
  results.append({'sample':sample,'byte_identical_outputs':matches,
    'cpu_hours_5_95':result['cpu_hours_5_95'],'cpu_hours':result['cpu_hours']})
print(json.dumps({'status':'PUBLISHED_ESTIMATE_REPRODUCED','commit':b['commit'],
 'python':sys.version,'replicates':20000,'random_seed':1,'uses_committed_default':True,
 'source_sha256':b['sha256'],'results':results},indent=2))
'''


def main():
    files = {n: subprocess.check_output(['git', 'show', COMMIT + ':' + PKG + n]).decode() for n in FILES}
    bundle = {'commit': COMMIT, 'files': files,
              'sha256': {n: hashlib.sha256(s.encode()).hexdigest() for n, s in files.items()}}
    code = 'import base64;exec(compile(base64.b64decode(' + repr(base64.b64encode(REMOTE.encode()).decode()) + '),"verify_fix.py","exec"))'
    result = subprocess.run(['/Users/rwalters/.local/bin/e85-remote', 'ssh', 'python3.12 -B -c ' + shlex.quote(code)],
                            input=json.dumps(bundle), capture_output=True, text=True)
    if result.returncode:
        print(result.stderr)
        raise SystemExit(result.returncode)
    data = json.loads(result.stdout)
    data['verifier_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    (ROOT / 'FIX_VERIFICATION.json').write_text(json.dumps(data, indent=2) + '\n')
    print(data['status'], data['results'])


if __name__ == '__main__':
    main()
