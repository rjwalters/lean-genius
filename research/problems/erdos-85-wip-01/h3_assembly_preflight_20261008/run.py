"""Cloud-only bounded compile of the conditional H3 assembly preflight."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib,json,os,resource,signal,subprocess,time
ROOT=Path(__file__).resolve().parent
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    assert Path('/.dockerenv').exists() and Path.cwd()==Path('/workspace/proofs')
    mem=int(Path('/sys/fs/cgroup/memory.max').read_text())
    cpu=Path('/sys/fs/cgroup/cpu.max').read_text().strip()
    quota,period=map(int,cpu.split())
    assert mem==16*1024**3 and quota==2*period
    spec=json.loads((ROOT/'SOURCE.json').read_text())
    source=ROOT/'H3AssemblyPreflight.lean'
    assert sha(source)==spec['preflight_source_sha256']
    prior=ROOT.parent/'h3_phase3_runtime_20261008/build-evidence/AUDIT.json'
    audit=json.loads(prior.read_text())
    assert audit['status']=='RUNTIME_HELPERS_CHAIN_BUILD_AUDIT_PASS'
    assert audit['execution_commit']==spec['math_commit']
    def check():
        for row in audit['results']:
            assert sha(Path('Proofs')/(row['module']+'.lean'))==row['source_sha256']
            assert sha(Path('.lake/build/lib/lean/Proofs')/(row['module']+'.olean'))==row['olean_sha256']
    check()
    stage=Path('H3AssemblyPreflight.lean')
    assert not stage.exists()
    out=ROOT/'attempt1';out.mkdir(exist_ok=False)
    obj=out/'H3AssemblyPreflight.olean'
    command=['lean','-j1',str(stage),'-o',str(obj)]
    report={'status':'RUNNING','started_utc':datetime.now(timezone.utc).isoformat(),
            'source_sha256':sha(source),'prerequisite_audit_sha256':sha(prior),
            'cgroup_memory_bytes':mem,'cgroup_cpu_max':cpu,'command':command,'timeout_seconds':90}
    start=time.monotonic(); before=resource.getrusage(resource.RUSAGE_CHILDREN)
    timed_out=False
    try:
        with stage.open('xb') as f:f.write(source.read_bytes())
        with (out/'compile.log').open('xb') as f:
            child=subprocess.Popen(command,stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
            try:rc=child.wait(timeout=90)
            except subprocess.TimeoutExpired:
                timed_out=True;os.killpg(child.pid,signal.SIGKILL);rc=child.wait()
        after=resource.getrusage(resource.RUSAGE_CHILDREN)
        report.update(returncode=rc,timed_out=timed_out,elapsed_seconds=time.monotonic()-start,
                      child_user_seconds=after.ru_utime-before.ru_utime,
                      child_system_seconds=after.ru_stime-before.ru_stime,
                      child_maxrss_kib=after.ru_maxrss,log_sha256=sha(out/'compile.log'))
        check()
        if rc==0:
            report.update(status='COMPILED_PENDING_AUDIT',object_sha256=sha(obj),
                          object_bytes=obj.stat().st_size,object_mtime=obj.stat().st_mtime)
        else:report['status']='TIMEOUT' if timed_out else 'COMPILE_FAILURE'
    finally:
        if stage.exists():stage.unlink()
        (out/'RUN.json').write_text(json.dumps(report,indent=2)+'\n')
        print(json.dumps(report,indent=2),flush=True)
        if (out/'compile.log').exists():print((out/'compile.log').read_text(),flush=True)
    return rc
if __name__=='__main__':raise SystemExit(main())
