import pathlib,json,time,hashlib,gzip,collections
from filter import check
P=pathlib.Path(__file__).parent;S=pathlib.Path('/tmp/erdos85-sol1-h7-crossed14-local/results.json');raw=S.read_bytes();source=json.loads(raw)
inputs=[(i,r) for i,r in enumerate(source['results']) if r['status']=='LOCAL_FEASIBLE'];out=[];start=time.monotonic();deadline=start+60
for i,r in inputs:
 if time.monotonic()>deadline:break
 a=check(r['adjacency'],max_nodes=100000,deadline=deadline);a['source_index']=i;out.append(a)
 if len(out)%50==0:print(len(out),dict(collections.Counter(x['status'] for x in out)),round(time.monotonic()-start,2),flush=True)
summary=dict(source_sha256=hashlib.sha256(raw).hexdigest(),total=len(inputs),visited=len(out),unvisited=len(inputs)-len(out),counts=dict(collections.Counter(x['status'] for x in out)),nodes=sum(x['nodes'] for x in out),seconds=time.monotonic()-start,scope='One bounded pass over448 crossed14 local survivors; UNKNOWN and unvisited not excluded. ARC_CONSISTENT is not graph existence.')
with gzip.open(P/'results.json.gz','wt') as f:json.dump(dict(summary=summary,results=out),f)
(P/'summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(summary,flush=True)
