AREA='research/problems/erdos-85-wip-01/h3_stratum_integration_20261008';JOB='20261008T145641-erdos85__h3-triple-formal-20261007-593077';PIN='80818771f0f157d0363b6d9d93b0afc8b9df9c04'
from pathlib import Path
import subprocess,json,base64,hashlib,re
repo=Path('/opt/e85/wt/erdos85__h3-triple-formal-20261007');root=repo/AREA;job=Path('/opt/e85/jobs')/JOB
assert (job/'exit').read_text().strip()=='0'
pid=int((job/'pid').read_text());assert not Path(f'/proc/{pid}').exists()
files={'job.'+n:(job/n).read_bytes() for n in ('log','spec','exit')}
assert re.findall(r'^\[e85\] commit ([a-f0-9]{40}) ',files['job.log'].decode(),re.M)==[PIN]
for name in ('SOURCE.json','INTEGRATION.json','transfer_pair.py'):
 data=(root/name).read_bytes();assert data==subprocess.check_output(['git','-C',str(repo),'show',PIN+':'+AREA+'/'+name]);files[name]=data
binding=json.loads(files['INTEGRATION.json'])
receipt=(root/'pair-transfer.json').read_bytes();r=json.loads(receipt)
assert r['status']=='PAIR_OBJECT_TRANSFER_VERIFIED' and r['triple_audit_sha256']==binding['triple_audit_sha256']
inspection=subprocess.check_output(['sudo','python3','-B',str(root/'transfer_pair.py'),'--triple-audit',str(repo/binding['triple_audit_path']),'--triple-audit-sha',binding['triple_audit_sha256']])
view=json.loads(inspection);assert view['status']=='PAIR_OBJECT_TRANSFER_PREFLIGHT_PASS'
assert len(view['objects'])==28 and view['objects']==r['after'] and all(x['destination_exists'] for x in view['objects'])
files['pair-transfer.json']=receipt;files['independent-inspection.json']=inspection
assert files['job.log']==(job/'log').read_bytes()
print(json.dumps({'files':{n:base64.b64encode(b).decode() for n,b in files.items()},'created':r['created']}))
