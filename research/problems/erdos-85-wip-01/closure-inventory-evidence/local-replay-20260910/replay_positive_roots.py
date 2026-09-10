from pathlib import Path
import json, hashlib, gzip, subprocess, time, datetime
C=Path('/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/campaign-20260825.noindex')
O=Path(__file__).resolve().parent/'small-high-positive-replay'
O.mkdir(exist_ok=True)
M=json.loads((C/'cube_jobs_manifest.live-38b15d484b.json').read_text())
BINS={'native':'/Volumes/Stripe/lean-genius/tools/drat-trim/lrat-check','lean':'/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration/proofs/.lake/build/bin/lratreplay'}
PINS={n:hashlib.sha256(Path(b).read_bytes()).hexdigest() for n,b in BINS.items()}
count=0
for cell in M['cells'].values():
    base=Path(cell['base']).read_bytes()
    if hashlib.sha256(base).hexdigest()!=cell['base_sha256']: raise ValueError('base hash')
    body=base.split(b'\n',1)[1]
    for job in cell['jobs']:
        gz=C/'tierA'/job['id']/'job.lrat.gz'
        if job['kind']!='cube' or not gz.is_file(): continue
        d=O/job['id']; d.mkdir(exist_ok=False)
        cnf=d/'job.cnf'; lrat=d/'job.lrat'
        cnf.write_bytes(f"p cnf {cell['variables']} {cell['base_clauses']+len(job['units'])}\n".encode()+body+b''.join(f'{u} 0\n'.encode() for u in job['units']))
        compressed=gz.read_bytes(); lrat.write_bytes(gzip.decompress(compressed))
        row={'job':job['id'],'scope':'existing local executable replay; no rebuild or generated theorem acceptance','started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'cnf_sha256':hashlib.sha256(cnf.read_bytes()).hexdigest(),'lrat_sha256':hashlib.sha256(lrat.read_bytes()).hexdigest(),'compressed_sha256':hashlib.sha256(compressed).hexdigest(),'runs':[],'accepted_current_stack':None}
        for name,binary in BINS.items():
            if hashlib.sha256(Path(binary).read_bytes()).hexdigest()!=PINS[name]: raise ValueError('binary drift')
            start=time.monotonic()
            try:
                r=subprocess.run([binary,str(cnf),str(lrat)],capture_output=True,text=True,timeout=60)
                run={'name':name,'binary':binary,'binary_sha256':PINS[name],'exit_code':r.returncode,'elapsed_s':time.monotonic()-start,'stdout':r.stdout,'stderr':r.stderr}
            except subprocess.TimeoutExpired:
                run={'name':name,'binary':binary,'binary_sha256':PINS[name],'timeout_s':60}
            row['runs'].append(run)
            (d/'receipt.json').write_text(json.dumps(row,indent=2)+'\n')
        cnf.unlink(); lrat.unlink();count+=1
        if count%16==0 or any(x.get('exit_code')!=0 for x in row['runs']): print(count,job['id'],[(x['name'],x.get('exit_code','timeout')) for x in row['runs']],flush=True)
print('COMPLETE',count,flush=True)
