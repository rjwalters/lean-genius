"""Cloud-only bounded assembly from exactly 384 independently accepted parts."""
import argparse,importlib.util,json,threading,time
from datetime import datetime,timezone
from pathlib import Path
from common import ROOT,REPO,sha,load_inputs,parse_axioms
def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--execute-approved-plan');args=p.parse_args()
    plan,manifest,prior,inputs=load_inputs()
    assert Path('/.dockerenv').exists() and Path.cwd()==Path('/workspace/proofs')
    memory=int(Path('/sys/fs/cgroup/memory.max').read_text());cpu=Path('/sys/fs/cgroup/cpu.max').read_text().strip()
    q,period=map(int,cpu.split());assert memory==16*1024**3 and q==2*period
    cache=Path('.lake/build/lib/lean/Proofs').resolve()
    def prerequisites():
        for row in prior['results']:
            assert sha((Path('Proofs')/(row['module']+'.lean')).read_bytes())==row['source_sha256']
            data=(cache/(row['module']+'.olean')).read_bytes()
            assert sha(data)==row['olean_sha256'] and len(data)==row['olean_bytes']
        for row in plan['parts']:
            data=(cache/(row['module'].split('.')[-1]+'.olean')).read_bytes()
            assert sha(data)==row['object_sha256'] and len(data)==row['object_bytes']
    prerequisites();out=ROOT/'attempt1';stop_path=ROOT/'STOP'
    module=plan['cell']['module'].split('.')[-1];source=Path('Proofs')/(module+'.lean');obj=cache/(module+'.olean')
    assert not out.exists() and not stop_path.exists() and not source.exists() and not obj.exists()
    plan_hash=sha((ROOT/'PLAN.json').read_bytes())
    if args.execute_approved_plan is None:
        print(json.dumps({'status':'READ_ONLY_PREFLIGHT_PASS','plan_sha256':plan_hash,'parts_checked':384,
                          'prerequisites_checked':4,'cgroup_memory_bytes':memory,'cgroup_cpu_max':cpu},indent=2));return 0
    assert args.execute_approved_plan==plan_hash
    helper=REPO/plan['inputs']['process_helper']['path'];spec=importlib.util.spec_from_file_location('bounded_process',helper)
    process=importlib.util.module_from_spec(spec);spec.loader.exec_module(process)
    out.mkdir();(out/'sources/Proofs').mkdir(parents=True)
    report={'status':'RUNNING','plan_sha256':plan_hash,'started_utc':datetime.now(timezone.utc).isoformat(),
            'cgroup_memory_bytes':memory,'cgroup_cpu_max':cpu,'imported_residues':list(range(384)),'scope':plan['scope']}
    def save():
        tmp=out/'RUN.json.tmp';tmp.write_text(json.dumps(report,indent=2)+'\n');tmp.replace(out/'RUN.json')
    owned=False;accepted=False;started=time.monotonic()
    try:
        save();(out/'sources'/source).write_bytes(inputs['cell_source'])
        with source.open('xb') as f:f.write(inputs['cell_source'])
        owned=True
        command=['lean','-j1',str(source),'-o',str(obj)]
        step=process.run_child(command,out/'compile.log',90,started+120,stop_path,threading.Event())
        report['step']=step;save();prerequisites()
        if step['stop_reason'] or step['returncode']!=0:
            report['status']=step['stop_reason'] or 'COMPILE_FAILURE';return 1
        data=obj.read_bytes();assert data;(out/obj.name).write_bytes(data)
        exports=parse_axioms((out/'compile.log').read_text(),plan['expected_exports'])
        report['cell']={'module':plan['cell']['module'],'source_sha256':sha(inputs['cell_source']),
                        'object_sha256':sha(data),'object_bytes':len(data),'object_mtime':obj.stat().st_mtime,'axiom_exports':exports}
        report['status']='CELL_COMPILED_PENDING_AUDIT';accepted=True;return 0
    except Exception as exc:
        report['status']='ALARM';report['exception']=repr(exc);raise
    finally:
        if owned:source.unlink()
        if owned and not accepted and obj.exists():
            data=obj.read_bytes();(out/'unaccepted.olean').write_bytes(data)
            report['unaccepted_object']={'sha256':sha(data),'bytes':len(data)};obj.unlink()
        report['elapsed_seconds']=time.monotonic()-started;save();print(json.dumps(report),flush=True)
if __name__=='__main__':raise SystemExit(main())
