"""Cloud-only residual pass; read-only preflight unless given the frozen plan hash."""
import argparse,importlib.util,json,threading,time
from datetime import datetime,timezone
from pathlib import Path
from common import ROOT,load_inputs,sha,parse_axioms,part_expectation
from process import run_child
from scheduler import run_pool

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--execute-approved-plan',help='Exact PLAN.json SHA-256 under room authorization 53044')
    args=parser.parse_args();plan,manifest,prior,inputs=load_inputs()
    assert Path('/.dockerenv').exists() and Path.cwd()==Path('/workspace/proofs')
    limits=plan['limits'];memory=int(Path('/sys/fs/cgroup/memory.max').read_text())
    cpu=Path('/sys/fs/cgroup/cpu.max').read_text().strip();quota,period=map(int,cpu.split())
    assert memory==limits['memory_gib']*1024**3 and quota==limits['cpus']*period
    cache=Path('.lake/build/lib/lean/Proofs').resolve();stop_path=ROOT/'STOP'
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
    init='initialize_proofs_Proofs_Erdos85H3TripleCompletionRuntime';assert init in cpath.read_text()
    for r in plan['residual_residues']:
        row=manifest['parts'][r]
        assert not Path(row['source_path']).exists()
        assert not (cache/(row['module'].split('.')[-1]+'.olean')).exists(),'Unaccepted object requires review'
    out=ROOT/'attempt1';assert not out.exists() and not stop_path.exists()
    if args.execute_approved_plan is None:
        print(json.dumps({'status':'READ_ONLY_PREFLIGHT_PASS','plan_sha256':sha((ROOT/'PLAN.json').read_bytes()),
                          'reused_objects_checked':len(plan['reused_parts']),'residual_residues':plan['residual_residues'],
                          'workers':limits['workers'],'cgroup_memory_bytes':memory,'cgroup_cpu_max':cpu},indent=2));return 0
    assert args.execute_approved_plan==sha((ROOT/'PLAN.json').read_bytes()),'Plan hash mismatch'
    generator_path=Path('/workspace')/plan['inputs']['generator']['path']
    spec=importlib.util.spec_from_file_location('frozen_h3_source_generator',generator_path)
    generator=importlib.util.module_from_spec(spec);spec.loader.exec_module(generator)
    out.mkdir();(out/'sources/Proofs').mkdir(parents=True);(out/'objects').mkdir();(out/'unaccepted-objects').mkdir()
    started=time.monotonic();deadline=started+limits['worker_seconds'];stop=threading.Event()
    report={'status':'RUNNING','started_utc':datetime.now(timezone.utc).isoformat(),'plan_sha256':args.execute_approved_plan,
            'workers':limits['workers'],'cgroup_memory_bytes':memory,'cgroup_cpu_max':cpu,
            'reused_residues':[r['residue'] for r in plan['reused_parts']],
            'steps':[],'parts':[],'attempts':[],'initializer':init,'scope':plan['scope']}
    def save():
        temp=out/'RUN.json.tmp';temp.write_text(json.dumps(report,indent=2)+'\n');temp.replace(out/'RUN.json')
    library=out/'libH3TripleRuntime.so'
    def work(r,event):
        row=manifest['parts'][r];name=f'part{r:03d}';rel=Path(row['source_path'])
        obj=cache/(row['module'].split('.')[-1]+'.olean');item={'residue':r,'status':'ALARM'}
        owned_source=False;accepted=False
        try:
            if event.is_set() or stop_path.exists():return {'residue':r,'status':'NOT_STARTED'}
            if time.monotonic()>=deadline:return {'residue':r,'status':'BUDGET_STOP'}
            prerequisites();source=generator.part_source(r).encode();assert sha(source)==row['source_sha256']
            assert not rel.exists() and not obj.exists()
            with (out/'sources'/rel).open('xb') as f:f.write(source)
            with rel.open('xb') as f:f.write(source)
            owned_source=True
            command=['lean','-j1','--plugin='+str(library)+'='+init,str(rel),'-o',str(obj)]
            result=run_child(command,out/(name+'.log'),limits['per_part_seconds'],deadline,stop_path,event)
            result['name']=name;item['step']=result
            if result['stop_reason'] or result['returncode']!=0:
                item['status']=result['stop_reason'] or 'COMPILE_FAILURE';return item
            content=obj.read_bytes();assert content
            with (out/'objects'/obj.name).open('xb') as f:f.write(content)
            exports=parse_axioms((out/(name+'.log')).read_text(),part_expectation(row))
            item.update(module=row['module'],source_sha256=sha(source),object_sha256=sha(content),object_bytes=len(content),
                        object_mtime=obj.stat().st_mtime,axiom_exports=exports,status='COMPILED_PENDING_AUDIT')
            accepted=True;return item
        except Exception as exc:
            event.set();item.update(status='ALARM',exception=repr(exc));return item
        finally:
            if owned_source:rel.unlink()
            # Retain any output from an unsuccessful invocation, then remove it from reuse.
            if owned_source and not accepted and obj.exists():
                data=obj.read_bytes();retained=out/'unaccepted-objects'/obj.name
                with retained.open('xb') as f:f.write(data)
                item['unaccepted_object']={'path':str(retained.relative_to(out)),'sha256':sha(data),'bytes':len(data)}
                obj.unlink()
    def record(item):
        report['attempts'].append(item)
        if 'step' in item:report['steps'].append(item['step'])
        if item['status']=='COMPILED_PENDING_AUDIT':
            report['parts'].append({k:v for k,v in item.items() if k!='step'})
        else:report['status']=item['status']
        save();print(json.dumps(item),flush=True)
    try:
        save()
        shared=run_child(['leanc','-O3','-DLEAN_EXPORTING','-shared','-fPIC',str(cpath),'-o',str(library)],
                         out/'shared.log',limits['library_seconds'],deadline,stop_path,stop)
        shared['name']='shared';report['steps'].append(shared);save()
        if shared['stop_reason'] or shared['returncode']!=0:
            report['status']=shared['stop_reason'] or 'COMPILE_FAILURE';return 1
        report['library']={'sha256':sha(library.read_bytes()),'bytes':library.stat().st_size};save()
        pool=run_pool(plan['residual_residues'],limits['workers'],work,record,stop)
        report['dispatched_residues']=pool['dispatched_residues'];report['not_started_residues']=pool['not_started_residues']
        prerequisites()
        if pool['stopped']:
            statuses={x['status'] for x in report['attempts']}
            report['status']=next((s for s in ('ALARM','TIMEOUT','BUDGET_STOP','COMPILE_FAILURE','STOP','NOT_STARTED') if s in statuses),'STOP')
            return 1
        assert sorted(x['residue'] for x in report['parts'])==plan['residual_residues']
        report['status']='RESIDUAL_COMPLETED_PENDING_AUDIT';return 0
    except Exception as exc:
        stop.set();report['status']='ALARM';report['exception']=repr(exc);raise
    finally:
        report['elapsed_seconds']=time.monotonic()-started;save()
        print(json.dumps({'status':report['status'],'completed_parts':len(report['parts'])}),flush=True)
if __name__=='__main__':raise SystemExit(main())
