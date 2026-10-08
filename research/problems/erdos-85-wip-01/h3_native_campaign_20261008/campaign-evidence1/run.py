"""Cloud-only bounded H3 campaign. Default operation is read-only preflight."""
import argparse,importlib.util,json,os,resource,signal,subprocess,time
from datetime import datetime,timezone
from pathlib import Path
from common import ROOT,load_inputs,sha,parse_axioms,part_expectation,cell_expectation

def step(command,log_path,cap,deadline,stop_path):
    before=resource.getrusage(resource.RUSAGE_CHILDREN);started=time.monotonic()
    effective=min(cap,max(0,deadline-started));reason=None
    if effective<=0 or stop_path.exists():raise RuntimeError('Stopped before child launch')
    with log_path.open('xb') as output:
        child=subprocess.Popen(command,stdout=output,stderr=subprocess.STDOUT,start_new_session=True)
        while True:
            if child.poll() is not None:break
            if stop_path.exists():reason='STOP'
            elif time.monotonic()-started>=effective:reason='TIMEOUT'
            if reason:
                try:os.killpg(child.pid,signal.SIGKILL)
                except ProcessLookupError:pass
                child.wait();break
            try:child.wait(timeout=min(0.25,max(0.01,effective-(time.monotonic()-started))))
            except subprocess.TimeoutExpired:pass
    after=resource.getrusage(resource.RUSAGE_CHILDREN)
    return {'command':command,'returncode':child.returncode,'stop_reason':reason,
            'timeout_seconds':cap,'effective_timeout_seconds':effective,'elapsed_seconds':time.monotonic()-started,
            'child_user_seconds':after.ru_utime-before.ru_utime,'child_system_seconds':after.ru_stime-before.ru_stime,
            'child_maxrss_kib_cumulative':after.ru_maxrss,'log_sha256':sha(log_path.read_bytes())}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--execute-approved-plan',help='Exact PLAN.json SHA-256, only after explicit launch authorization')
    args=parser.parse_args();plan,manifest,prior,inputs=load_inputs()
    assert Path('/.dockerenv').exists() and Path.cwd()==Path('/workspace/proofs')
    memory=int(Path('/sys/fs/cgroup/memory.max').read_text());cpu=Path('/sys/fs/cgroup/cpu.max').read_text().strip()
    quota,period=map(int,cpu.split());assert memory==16*1024**3 and quota==2*period
    cache=Path('.lake/build/lib/lean/Proofs').resolve();stopped=ROOT/'STOP'
    def prerequisites():
        for row in prior['results']:
            assert sha((Path('Proofs')/(row['module']+'.lean')).read_bytes())==row['source_sha256']
            assert sha((cache/(row['module']+'.olean')).read_bytes())==row['olean_sha256']
        for row in plan['reused_parts']:
            data=(cache/(row['module'].split('.')[-1]+'.olean')).read_bytes()
            assert sha(data)==row['object_sha256'] and len(data)==row['object_bytes']
    prerequisites()
    cpath=Path('.lake/build/ir/Proofs/Erdos85H3TripleCompletionRuntime.c').resolve()
    assert sha(cpath.read_bytes())==prior['runtime_c']['sha256']
    init='initialize_proofs_Proofs_Erdos85H3TripleCompletionRuntime'
    assert init in cpath.read_text()
    for r in plan['remaining_residues']:
        row=manifest['parts'][r]
        assert not Path(row['source_path']).exists()
        assert not (cache/(row['module'].split('.')[-1]+'.olean')).exists()
    cell_name=manifest['cell']['module'].split('.')[-1]
    assert not Path('Proofs',cell_name+'.lean').exists() and not (cache/(cell_name+'.olean')).exists()
    assert not (ROOT/'attempt1').exists() and not stopped.exists()
    if args.execute_approved_plan is None:
        print(json.dumps({'status':'READ_ONLY_PREFLIGHT_PASS','plan_sha256':sha((ROOT/'PLAN.json').read_bytes()),
              'reused_objects_checked':5,'new_parts':379,'cgroup_memory_bytes':memory,'cgroup_cpu_max':cpu,
              'scope':'No compilation, native search, artifact changes or launch authorization.'},indent=2));return 0
    assert args.execute_approved_plan==sha((ROOT/'PLAN.json').read_bytes()),'Plan hash mismatch'
    generator_path=Path('/workspace')/plan['inputs']['generator']['path']
    spec=importlib.util.spec_from_file_location('frozen_h3_source_generator',generator_path)
    generator=importlib.util.module_from_spec(spec);spec.loader.exec_module(generator)
    out=ROOT/'attempt1';out.mkdir();(out/'sources/Proofs').mkdir(parents=True);(out/'objects').mkdir()
    started=time.monotonic();deadline=started+plan['limits']['worker_seconds']
    report={'status':'RUNNING','started_utc':datetime.now(timezone.utc).isoformat(),'plan_sha256':args.execute_approved_plan,
            'cgroup_memory_bytes':memory,'cgroup_cpu_max':cpu,'reused_residues':[r['residue'] for r in plan['reused_parts']],
            'steps':[],'parts':[],'initializer':init,'scope':plan['scope']}
    def save():
        temp=out/'RUN.json.tmp';temp.write_text(json.dumps(report,indent=2)+'\n');temp.replace(out/'RUN.json')
    def run_step(name,command,cap):
        result=step(command,out/(name+'.log'),cap,deadline,stopped);result['name']=name
        report['steps'].append(result);save();print(json.dumps(result),flush=True)
        if result['returncode']!=0 or result['stop_reason']:
            report['status']=result['stop_reason'] or 'COMPILE_FAILURE';return False
        return True
    def compile_source(name,module,data,expected,cap,plugin=None):
        rel=Path('Proofs')/(module+'.lean');obj=cache/(module+'.olean')
        assert not rel.exists() and not obj.exists()
        (out/'sources'/rel).write_bytes(data)
        with rel.open('xb') as f:f.write(data)
        try:
            command=['lean','-j1']+(['--plugin='+str(plugin)+'='+init] if plugin else [])+[str(rel),'-o',str(obj)]
            ok=run_step(name,command,cap)
        finally:rel.unlink()
        if not ok:return None
        content=obj.read_bytes();assert content
        # Preserve compiled bytes even if the subsequent axiom check rejects them.
        (out/'objects'/obj.name).write_bytes(content)
        result={'module':'Proofs.'+module,'source_sha256':sha(data),'object_sha256':sha(content),
                'object_bytes':len(content),'object_mtime':obj.stat().st_mtime,
                'axiom_exports':parse_axioms((out/(name+'.log')).read_text(),expected),'status':'COMPILED_PENDING_AUDIT'}
        return result
    try:
        save();library=out/'libH3TripleRuntime.so'
        if not run_step('shared',['leanc','-O3','-DLEAN_EXPORTING','-shared','-fPIC',str(cpath),'-o',str(library)],60):return 1
        report['library']={'sha256':sha(library.read_bytes()),'bytes':library.stat().st_size};save()
        for r in plan['remaining_residues']:
            if stopped.exists() or time.monotonic()>=deadline:
                report['status']='STOP' if stopped.exists() else 'TIMEOUT';return 1
            prerequisites();row=manifest['parts'][r];source=generator.part_source(r).encode()
            assert sha(source)==row['source_sha256']
            item=compile_source(f'part{r:03d}',row['module'].split('.')[-1],source,part_expectation(row),90,library)
            if item is None:return 1
            item['residue']=r;report['parts'].append(item);save()
        prerequisites()
        assert len(report['parts'])+len(plan['reused_parts'])==384
        for item in report['parts']:
            assert sha((cache/(item['module'].split('.')[-1]+'.olean')).read_bytes())==item['object_sha256']
        if stopped.exists() or time.monotonic()>=deadline:
            report['status']='STOP' if stopped.exists() else 'TIMEOUT';return 1
        cell=compile_source('cell',cell_name,inputs['cell_source'],cell_expectation(manifest),90)
        if cell is None:return 1
        report['cell']=cell;prerequisites();report['status']='FULL_COMPILED_PENDING_AUDIT';return 0
    except Exception as exc:
        report['status']='ALARM';report['exception']=repr(exc);raise
    finally:
        report['elapsed_seconds']=time.monotonic()-started;save();print(json.dumps({'status':report['status'],'completed_parts':len(report['parts'])}),flush=True)
if __name__=='__main__':raise SystemExit(main())
