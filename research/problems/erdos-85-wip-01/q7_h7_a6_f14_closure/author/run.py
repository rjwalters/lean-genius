"""One bounded necessary S-P projection pass on the exact reviewed F14 suffix."""
import collections,gzip,hashlib,importlib.util,json,sqlite3,time
from pathlib import Path
P=Path(__file__).parent;A=Path('/Users/rwalters/lean-genius-h7-a6-f14-incidence-native-sol2-20260915');B=Path('/Users/rwalters/lean-genius-h7-a6-f14-sol1-20260915');T=Path('/Users/rwalters/lean-genius-h7-a6-f14-triangle-sol1-20260915');S=B/'hosts'
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 assert not (P/'launch.json').exists(),'No overwrite or capped restart'
 reviews={};db=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True)
 for rid in [2707,2714,2716,2717]:
  st,res=db.execute('select status,resolution from review_requests where id=?',(rid,)).fetchone();assert st=='resolved' and res.startswith('PASS');reviews[rid]=res
 for base,manifest in [(A,'pins.json'),(B,'host-pins.json'),(T,'pins.json')]:
  for n,h in read(base/manifest).items():assert sha(base/n)==h,n
 queue=read(T/'repaired/results.json')['remaining'];assert len(queue)==445699 and len(set(map(tuple,queue)))==445699
 wanted={}
 for gid,j in queue:wanted.setdefault(gid,[]).append(j)
 inputs={r['global_index']:[sum(1<<v for v in ns) for ns in r['neighbors']] for r in map(json.loads,gzip.open(B/'inputs.jsonl.gz','rt')) if r['global_index'] in wanted}
 assert set(inputs)==set(wanted)
 sp=importlib.util.spec_from_file_location('reviewed_projection_api',A/'api.py');mod=importlib.util.module_from_spec(sp);sp.loader.exec_module(mod);api=mod.ProjectionAPI()
 launch={'total':445699,'aggregate_seconds':300,'nodes_per_case':10000,'shard_byte_cap':50000000,'artifact_byte_cap':200000000,'batch_raw_target':524288,'source_remaining_sha256':sha(T/'repaired/results.json'),'source_host_pins_sha256':sha(B/'host-pins.json'),'api_pins_sha256':sha(A/'pins.json'),'driver_sha256':sha(Path(__file__)),'reviews':reviews}
 (P/'launch.json').write_text(json.dumps(launch,indent=2)+'\n')
 start=time.monotonic();deadline=start+300;attempted=visited=nodes=size=allsize=0;counts=collections.Counter();retained=[];shards=[];stream=None;pending=[];pending_info=[];rawsize=0;stop=None
 def flush():
  nonlocal visited,nodes,size,allsize,stream,pending,pending_info,rawsize
  if not pending:return True
  blob=gzip.compress(b''.join(pending),compresslevel=1,mtime=0)
  if len(blob)>50000000 or allsize+len(blob)>200000000:return False
  if stream is None or size+len(blob)>50000000:
   if stream:stream.close()
   name=f'receipts-{len(shards):03d}.jsonl.gz';shards.append(name);stream=(P/name).open('xb');size=0
  stream.write(blob);size+=len(blob);allsize+=len(blob)
  for gid,j,st,n in pending_info:
   assert queue[visited]==[gid,j];visited+=1;nodes+=n;counts[st]+=1
   if st not in ['EMPTY_FAMILY','INFEASIBLE_PROJECTION']:retained.append([gid,j,st])
  pending=[];pending_info=[];rawsize=0;return True
 try:
  for name in read(S/'results.json')['shards']:
   for host in map(json.loads,gzip.open(S/name,'rt')):
    gid=host['global_index']
    if gid not in wanted:continue
    assert host['receipt']['status']=='COMPLETE'
    for j in wanted[gid]:
     if time.monotonic()>=deadline:stop='AGGREGATE_CAP';break
     assert queue[attempted]==[gid,j];g=inputs[gid][:]
     for e,m in enumerate(host['receipt']['solutions'][j],42):
      g[e]|=m
      while m:
       b=m&-m;m-=b;g[b.bit_length()-1]|=1<<e
     cert=api.check(g,max_nodes=10000,deadline=deadline);attempted+=1
     record={'global_index':gid,'leaf_index':j,'certificate':cert};blob=(json.dumps(record,separators=(',',':'))+'\n').encode()
     pending.append(blob);pending_info.append((gid,j,cert['status'],cert.get('nodes',0)));rawsize+=len(blob)
     if rawsize>=524288 and not flush():stop='ARTIFACT_CAP';break
     if cert['status']=='INVALID':stop='INVALID_INPUT';break
    if stop:break
   if stop:break
  if stop!='ARTIFACT_CAP' and not flush():stop='ARTIFACT_CAP'
 finally:
  if stream:stream.close()
 out={'total':445699,'attempted':attempted,'visited':visited,'unvisited':445699-visited,'counts':dict(counts),'retained':retained,'nodes':nodes,'artifact_bytes':allsize,'computed_not_saved':attempted-visited,'shards':shards,'seconds':time.monotonic()-start,'stop':stop,'scope':'Necessary singleton-pair incidence only. Positive/UNKNOWN/INVALID/unvisited not exclusions; missing pair-pair edges omitted.'}
 (P/'results.json').write_text(json.dumps(out,indent=2)+'\n');(P/'unvisited.json').write_text(json.dumps(queue[visited:],separators=(',',':'))+'\n');print(json.dumps({k:v for k,v in out.items() if k!='retained'}))
if __name__=='__main__':main()
