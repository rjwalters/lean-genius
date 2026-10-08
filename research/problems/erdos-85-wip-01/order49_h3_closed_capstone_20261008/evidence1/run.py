"""Cloud-only direct Lean compile of the three H1/H7-conditional corollaries."""
import json,os,re,signal,subprocess,time
from datetime import datetime,timezone
from pathlib import Path
from prepare import ROOT,REPO,MODULE,sha,inputs,closure
def main():
    assert Path('/.dockerenv').exists() and Path.cwd()==Path('/workspace/proofs')
    plan=json.loads((ROOT/'PLAN.json').read_text());_,objects,producers,exports=inputs()
    assert plan['objects']==objects and plan['producers']==producers and plan['exports']==exports
    assert plan['sources']==closure(REPO,MODULE)
    transfer=json.loads((ROOT/'transfer.json').read_text())
    assert transfer['status']=='CAPSTONE_OBJECT_TRANSFER_VERIFIED' and transfer['plan_sha256']==sha((ROOT/'PLAN.json').read_bytes())
    assert len(transfer['after'])==500 and all(x['destination_exists'] for x in transfer['after'])
    memory=int(Path('/sys/fs/cgroup/memory.max').read_text());cpu=Path('/sys/fs/cgroup/cpu.max').read_text().strip()
    quota,period=map(int,cpu.split());assert memory==16*1024**3 and quota==2*period
    cache=Path('.lake/build/lib/lean/Proofs').resolve();obj=cache/(MODULE+'.olean');assert not obj.exists()
    def check():
        assert plan['sources']==closure(REPO,MODULE)
        for m,row in objects.items():
            b=(cache/(m+'.olean')).read_bytes();assert sha(b)==row['sha256'] and len(b)==row['bytes'],m
    check();out=ROOT/'attempt2';out.mkdir(exist_ok=False)
    # Validate the extra baseline dependency without replacing its cache object.
    supplement=json.loads((ROOT/'supplementary.json').read_text())
    assert plan['supplementary_sha256']==sha((ROOT/'supplementary.json').read_bytes())
    baseline=supplement['module'];fresh=out/(baseline+'.olean')
    rebuild=json.loads((ROOT/'REBUILD.json').read_text())
    assert sha((ROOT/'baseline.setup.json').read_bytes())==rebuild['setup_sha256']
    assert sha((ROOT/'baseline.trace').read_bytes())==rebuild['trace_sha256']
    baseline_command=['lean','-j1',str(REPO/'proofs/Proofs'/(baseline+'.lean')),'-o',str(fresh),'-i',str(out/(baseline+'.ilean')),'-c',str(out/(baseline+'.c')),'--setup',str(ROOT/'baseline.setup.json'),'--json']
    baseline_start=time.monotonic()
    with (out/'baseline.log').open('xb') as log:
        child=subprocess.Popen(baseline_command,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
        try:baseline_rc=child.wait(timeout=90)
        except subprocess.TimeoutExpired:
            os.killpg(child.pid,signal.SIGKILL);child.wait();raise RuntimeError('Baseline rebuild timed out')
    assert baseline_rc==0 and not re.search(r'\b(sorry|error)\b',(out/'baseline.log').read_text(),re.I)
    baseline_data=fresh.read_bytes()
    assert sha(baseline_data)==supplement['sha256'] and len(baseline_data)==supplement['bytes'],'Baseline rebuilt object differs'
    baseline_receipt={'status':'BASELINE_REBUILD_BYTE_IDENTICAL','command':baseline_command,'returncode':baseline_rc,'elapsed_seconds':time.monotonic()-baseline_start,'sha256':sha(baseline_data),'bytes':len(baseline_data),'log_sha256':sha((out/'baseline.log').read_bytes()),'setup_sha256':rebuild['setup_sha256'],'trace_sha256':rebuild['trace_sha256']}
    (out/'BASELINE.json').write_text(json.dumps(baseline_receipt,indent=2)+'\n')
    check()
    command=['lean','-j1','Proofs/'+MODULE+'.lean','-o',str(obj)]
    report={'status':'RUNNING','started_utc':datetime.now(timezone.utc).isoformat(),'command':command,'timeout_seconds':90,'cgroup_memory_bytes':memory,'cgroup_cpu_max':cpu,'plan_sha256':sha((ROOT/'PLAN.json').read_bytes()),'transfer_sha256':sha((ROOT/'transfer.json').read_bytes())}
    start=time.monotonic();timed_out=False;rc=1
    try:
        with (out/'compile.log').open('xb') as log:
            child=subprocess.Popen(command,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
            try:rc=child.wait(timeout=90)
            except subprocess.TimeoutExpired:timed_out=True;os.killpg(child.pid,signal.SIGKILL);rc=child.wait()
        report.update(returncode=rc,timed_out=timed_out,elapsed_seconds=time.monotonic()-start,log_sha256=sha((out/'compile.log').read_bytes()))
        check()
        if rc==0 and not timed_out:
            raw=(out/'compile.log').read_text();assert not re.search(r'\b(sorry|error)\b',raw,re.I)
            matches=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",raw);assert len(matches)==3
            actual=[]
            for (name,rawaxioms),expected in zip(matches,exports):
                axioms=[x.strip() for x in rawaxioms.split(',') if x.strip()]
                assert name==expected['theorem'] and len(axioms)==len(set(axioms)) and sorted(axioms)==expected['axioms']
                actual.append({'theorem':name,'axioms':axioms})
            data=obj.read_bytes();assert data;(out/obj.name).write_bytes(data)
            report.update(status='CAPSTONE_H3_COMPILED_PENDING_AUDIT',exports=actual,object={'sha256':sha(data),'bytes':len(data),'mtime':obj.stat().st_mtime})
        else:report['status']='TIMEOUT' if timed_out else 'COMPILE_FAILURE'
    except Exception as exc:report.update(status='ALARM',exception=repr(exc));raise
    finally:
        (out/'RUN.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2),flush=True)
        if (out/'compile.log').exists():print((out/'compile.log').read_text(),flush=True)
    return 1 if timed_out else rc
if __name__=='__main__':raise SystemExit(main())
