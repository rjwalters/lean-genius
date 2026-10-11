"""Cloud-only bounded compile of the H3 stratum from 417 audited imported objects."""
import argparse,json,os,re,resource,signal,subprocess,time
from datetime import datetime,timezone
from pathlib import Path
from transfer_pair import ROOT,REPO,sha
from stratum_inputs import load

def main():
    p=argparse.ArgumentParser();p.add_argument('--triple-audit-sha',required=True);p.add_argument('--transfer-receipt-sha',required=True);a=p.parse_args()
    assert all(re.fullmatch(r'[a-f0-9]{64}',s) for s in vars(a).values())
    assert Path('/.dockerenv').exists() and Path.cwd()==Path('/workspace/proofs')
    spec,objects,inputs=load(ROOT,REPO,a.triple_audit_sha,a.transfer_receipt_sha)
    memory=int(Path('/sys/fs/cgroup/memory.max').read_text());cpu=Path('/sys/fs/cgroup/cpu.max').read_text().strip()
    quota,period=map(int,cpu.split());assert memory==16*1024**3 and quota==2*period
    cache=Path('.lake/build/lib/lean/Proofs').resolve();obj=cache/'Erdos85H3Stratum.olean'
    assert not obj.exists()
    def prerequisites():
        for module,row in objects.items():
            data=(cache/(module+'.olean')).read_bytes()
            assert sha(data)==row['sha256'] and len(data)==row['bytes'],module
    prerequisites();out=ROOT/'stratum-attempt1';out.mkdir(exist_ok=False)
    for name,data in inputs.items():(out/name).write_bytes(data)
    command=['lean','-j1','Proofs/Erdos85H3Stratum.lean','-o',str(obj)]
    report={'status':'RUNNING','started_utc':datetime.now(timezone.utc).isoformat(),'command':command,
            'timeout_seconds':90,'cgroup_memory_bytes':memory,'cgroup_cpu_max':cpu,
            'input_sha256':{n:sha(b) for n,b in inputs.items()},'imported_objects':objects}
    start=time.monotonic();before=resource.getrusage(resource.RUSAGE_CHILDREN);timed_out=False
    try:
        with (out/'compile.log').open('xb') as log:
            child=subprocess.Popen(command,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
            try:rc=child.wait(timeout=90)
            except subprocess.TimeoutExpired:
                timed_out=True;os.killpg(child.pid,signal.SIGKILL);rc=child.wait()
        after=resource.getrusage(resource.RUSAGE_CHILDREN)
        report.update(returncode=rc,timed_out=timed_out,elapsed_seconds=time.monotonic()-start,
                      child_user_seconds=after.ru_utime-before.ru_utime,child_system_seconds=after.ru_stime-before.ru_stime,
                      child_maxrss_kib=after.ru_maxrss,log_sha256=sha((out/'compile.log').read_bytes()))
        prerequisites()
        if rc==0:
            data=obj.read_bytes();assert data;(out/obj.name).write_bytes(data)
            raw=(out/'compile.log').read_text();assert not re.search(r'\b(sorry|error)\b',raw,re.I)
            reports=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",raw)
            assert len(reports)==1 and reports[0][0]==spec['stratum_export']
            axioms=[x.strip() for x in reports[0][1].split(',') if x.strip()]
            assert len(axioms)==len(set(axioms))==411 and set(axioms)==set(spec['expected_stratum_axioms'])
            report.update(status='STRATUM_COMPILED_PENDING_AUDIT',axioms=axioms,object_sha256=sha(data),
                          object_bytes=len(data),object_mtime=obj.stat().st_mtime)
        else:report['status']='TIMEOUT' if timed_out else 'COMPILE_FAILURE'
    except Exception as exc:
        report['status']='ALARM';report['exception']=repr(exc);raise
    finally:
        (out/'RUN.json').write_text(json.dumps(report,indent=2)+'\n')
        print(json.dumps(report,indent=2),flush=True)
        if (out/'compile.log').exists():print((out/'compile.log').read_text(),flush=True)
    return rc
if __name__=='__main__':raise SystemExit(main())
