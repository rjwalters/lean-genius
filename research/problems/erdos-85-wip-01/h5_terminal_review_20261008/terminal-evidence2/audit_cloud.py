"""Read-only terminal H5 evidence collection. No Lean execution or peer mutations."""
import base64,hashlib,json,re,subprocess
from pathlib import Path
from datetime import datetime
from validate_axioms import check_reports
REPO=Path('/opt/e85/wt/erdos85__h5-formal-20261008')
JOB=Path('/opt/e85/jobs/20261008T112746-erdos85__h5-formal-20261008-455708')
COMMIT='99bc3e3413008ca13d5efb29bee5e855af961976'
CACHE=Path('/var/lib/docker/volumes/lean-build-erdos85__h5-formal-20261008/_data/lib/lean/Proofs')
def sha(data):return hashlib.sha256(data).hexdigest()
def require(ok,message):
    if not ok:raise ValueError(message)
def object_infos(modules):
    script='''import pathlib,hashlib,json,sys
base=pathlib.Path(sys.argv[1]);result={}
for m in sys.argv[2:]:
 p=base/(m+'.olean')
 if p.exists():
  s=p.stat();result[m]={'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':s.st_size,'mtime':s.st_mtime}
 else:result[m]=None
print(json.dumps(result))'''
    return json.loads(subprocess.check_output(['sudo','python3','-c',script,str(CACHE),*modules],text=True))
def main(config):
    inv=config['inventory']; graph=config['graph_review']; prior=config['prerequisites']
    require(inv['execution_commit']==COMMIT and inv['intended_job']==JOB.name,'Wrong inventory pin')
    if not (JOB/'exit').exists():
        pid=int((JOB/'pid').read_text())
        print(json.dumps({'status':'PENDING','job':JOB.name,'pid':pid,'pid_live':Path(f'/proc/{pid}').exists()}));return
    files={'job.'+n:(JOB/n).read_bytes() for n in ('log','spec','exit')}
    raw=files['job.log'].decode();rc=int(files['job.exit'])
    report={'job':JOB.name,'execution_commit':COMMIT,'authoritative_exit':rc,'status':'REJECTED','problems':[],
            'results':[],'prerequisites':[],'graph_modules':[],'scope':'Whole H5 stratum acceptance requires all 40 parts, all four assemblies and exact reviewed graph-cover axioms.'}
    try:
        require(re.findall(r'^\[e85\] commit ([a-f0-9]{40}) ',raw,re.M)==[COMMIT],'Execution commit mismatch')
        for line in ('MODE=build','REF=erdos85/h5-formal-20261008','TARGET=Proofs.Erdos85H5Stratum','MEM_GB=48','TIMEOUT=6h','THREADS=8','CPUS=16'):
            require(line in files['job.spec'].decode().splitlines(),'Specification mismatch: '+line)
        require(rc==0,'Authoritative build exit is not zero')
        require('Build completed successfully (' in raw and '=== Build succeeded ===' in raw,'Missing build completion banners')
        require(not re.search(r'\berror:',raw,re.I) and 'sorry' not in raw.lower(),'Build error or sorry warning')
        start_match=re.search(r'^\[e85\] job .* started (\S+)',raw,re.M)
        require(start_match is not None,'Missing start timestamp')
        start=datetime.fromisoformat(start_match[1].replace('Z','+00:00')).timestamp();finish=(JOB/'exit').stat().st_mtime
        dependency=config['graph_dependency_audit']
        require(dependency['status']=='H5_GRAPH_DEPENDENCY_ARTIFACT_AUDIT_PASS','Graph dependencies not audited')
        require(dependency['h5_execution_commit']==COMMIT,'Graph dependency H5 pin mismatch')
        graph_rows={r['module']:r for r in dependency['results']}
        require(len(graph_rows)==len(dependency['results']),'Duplicate graph dependency')
        require(set(graph['sources'])<=set(graph_rows),'Missing audited graph source')
        modules=list(inv['sources']); graph_modules=list(graph_rows)
        require(len(modules)==44 and len(set(modules))==44,'Wrong inventory size')
        all_modules=modules+[p['module'] for p in prior]+graph_modules
        require(len(all_modules)==len(set(all_modules)),'Overlapping module inventories')
        objects=object_infos(all_modules)
        def source(module,expected):
            path='proofs/Proofs/'+module+'.lean'
            data=subprocess.check_output(['git','-C',str(REPO),'show',COMMIT+':'+path])
            require(data==(REPO/path).read_bytes(),'Pinned/current source mismatch: '+module)
            require(sha(data)==expected,'Reviewed source hash mismatch: '+module)
            files['sources/'+module+'.lean']=data
            require(not re.search(r'\b(sorry|unsafe|implemented_by)\b',data.decode()),'Source trust escape: '+module)
            require(not re.search(r'^\s*(?:private\s+)?axiom\s',data.decode(),re.M),'Explicit axiom: '+module)
            return data
        for module,entry in inv['sources'].items():
            data=source(module,entry['sha256'])
            built=re.findall(r'\] Built Proofs\.'+re.escape(module)+r' \(([^)]+)\)',raw)
            require(len(built)==1,'Expected one fresh build: '+module)
            obj=objects[module];require(obj is not None and obj['bytes']>0,'Missing object: '+module)
            require(start<=obj['mtime']<=finish,'Object outside job interval: '+module)
            report['results'].append({'module':module,'source_sha256':sha(data),'object':obj,'fresh_build_elapsed':built[0]})
        for entry in prior:
            module=entry['module'];source(module,entry['source_sha256']);obj=objects[module]
            require(obj is not None and obj['sha256']==entry['olean_sha256'],'Audited dependency object changed: '+module)
            report['prerequisites'].append({'module':module,'source_sha256':entry['source_sha256'],'object':obj})
        for module,entry in graph_rows.items():
            if module in graph['sources']:
                require(entry['source_sha256']==graph['sources'][module]['sha256'],'Graph review source differs: '+module)
            source(module,entry['source_sha256']);obj=objects[module]
            require(obj is not None and obj['bytes']>0 and obj['mtime']<=finish,'Missing graph dependency: '+module)
            require(obj==entry['object'],'Audited graph dependency changed: '+module)
            report['graph_modules'].append({'module':module,'source_sha256':entry['source_sha256'],'object':obj})
        report['axiom_check']=check_reports(raw,inv,graph)
        report['problems'].extend(report['axiom_check']['problems'])
        require(objects==object_infos(all_modules),'Objects changed during collection')
        for name,data in list(files.items()):
            if name.startswith('sources/'):
                require(data==(REPO/'proofs/Proofs'/name.split('/')[-1]).read_bytes(),'Source changed during collection')
        require(files['job.log']==(JOB/'log').read_bytes(),'Terminal log changed')
        status=report['axiom_check']['status']
        report['status']='H5_STRATUM_ARTIFACT_AUDIT_PASS' if status=='AXIOM_SETS_PASS' else status
    except (ValueError,FileNotFoundError,subprocess.CalledProcessError) as exc:
        report['problems'].append(str(exc))
    report['retained_sha256']={n:sha(b) for n,b in files.items()}
    print(json.dumps({'audit':report,'files':{n:base64.b64encode(b).decode() for n,b in files.items()}}))
