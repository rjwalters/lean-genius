from pathlib import Path
import json,hashlib,sqlite3,itertools as I,time,numpy as np,math
p=Path(__file__).parent;b=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3');read=lambda f:json.loads(f.read_text());hashes={}
for name in ['residual-ten-D5-five-311-nonempty-joint','residual-ten-D5-five-311-nonempty-low-integer']:
 for mf in ['pins.json','input-pins.json']:
  for n,h in read(b/name/mf).items():
   f=b/name/n;assert hashlib.sha256(f.read_bytes()).hexdigest()==h;hashes[str(f)]=h
con=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True);con.row_factory=sqlite3.Row
states=[dict(con.execute('select id,status,resolution from review_requests where id=?',(i,)).fetchone()) for i in [2440,2460,2463,2467,2468,2469]];assert all(x['status']=='resolved' and x['resolution'].startswith('PASS') for x in states)
alloc=read(b/'residual-ten-D5-five-311-fixed-allocation/results.json')['records'];graphs={x['root']:x for x in read(b/'residual-ten-D5-five-311-high-matchings/results.json')['records']};pack=read(b/'residual-ten-D5-five-311-packing/results.json')['records'];classes=read(b/'residual-ten-D5-supports/results.json')['records'];saved=read(b/'residual-ten-D5-five-311-nonempty-joint/results.json');assert saved['status']=='COMPLETE';savedmap={x['root']:x for x in saved['records']}
expected=[s for s in alloc if s['status']=='EXACT_RATIONAL_WITNESS' and graphs[s['packing_root']]['survivors'][s['graph']]['edges']];assert len(expected)==len(savedmap)==len(saved['records'])==375 and set(savedmap)=={s['root'] for s in expected}
def flip(m):return sum(1<<(e^1) for e in range(10) if m&(1<<e))
start=time.monotonic();out=[];status='INCOMPLETE';contexts={}
try:
 for source in expected:
  if time.monotonic()-start>30:raise TimeoutError
  ci,ri=source['class'],source['source_root'];g=graphs[source['packing_root']]['survivors'][source['graph']];root=pack[ci]['survivors'][ri];saved=savedmap[source['root']]
  assert all(source[k]==saved[k] for k in ['root','class','source_root','packing_root','graph']) and saved['status']=='COMPLETE'
  R=np.zeros((10,10),dtype=np.int64)
  for v,w in classes[ci]['edges']:R[v,w]=R[w,v]=1
  assert np.all(R.sum(1)==1)
  primary=[classes[ci]['high3'][j] for j in root['high3']];supports=[s for x in primary for s in (x,[e^1 for e in x])];S=np.array([[int(e in s) for e in range(10)] for s in supports],dtype=np.int64)
  A=np.zeros((20,20),dtype=np.int64);A[:10,:10]=R;A[10:,:10]=S;A[:10,10:]=S.T
  for v,w in g['edges']:A[10+v,10+w]=A[10+w,10+v]=1
  A2=A@A;covered=A2[10:,:10]>0;Z=((A2[:10,:10]==0)&(~np.eye(10,dtype=bool))).astype(np.int64);D=R@Z-Z@R
  low=9-R.sum(1)-S.sum(0);q=6-R.sum(1)-Z.sum(1);assert q.tolist()==root['q']
  domains=[sorted(m for m in g['Q_domains'][v] if flip(m) in g['Q_domains'][v+1]) for v in range(0,10,2)];assert all(len(ds)==len(set(ds)) for ds in domains)
  ids=np.indices(tuple(map(len,domains))).reshape(5,-1).T;N=len(ids);assert N==saved['products'];Q=np.zeros((N,10,10),dtype=np.int64)
  for v,ds in enumerate(domains):
   options=np.array([[[int(mask&(1<<e)>0) for e in range(10)] for mask in [m,flip(m)]] for m in ds],dtype=np.int64);Q[:,2*v:2*v+2,:]=options[ids[:,v]]
  columns=Q.sum(1);left=q-columns;inactive=low-(~covered).sum(0)+columns
  keep=np.all(left>=0,1)&np.all(inactive>=0,1);assert int(keep.sum())==saved['column_capacity']
  ids=ids[keep];Q=Q[keep];left=left[keep];inactive=inactive[keep]
  T=D-(Q.transpose(0,2,1)@S-S.T@Q);P=np.maximum(-T,0);positive=np.maximum(T,0).sum(2)
  flow=np.all(left-T.sum(2)==2*inactive,1)&np.all(positive<=left,1)&np.all(P.max(2)<=inactive,1)&np.all(T[:,R.astype(bool)]==0,1)
  assert int(flow.sum())==saved['flow']
  ids=ids[flow];Q=Q[flow];left=left[flow];inactive=inactive[flow];T=T[flow];positive=positive[flow]
  parity=(low-((~covered)[None,:,:]-Q)*S[None,:,:]).sum(1) if False else (low-(((~covered)[None,:,:]-Q)*S[None,:,:]).sum(1))%2
  keep=np.all(parity<=np.minimum(left-positive,inactive),1)
  actual={};context=[]
  for k in np.flatnonzero(keep):
   rows=tuple(domains[v][z] for v,z in enumerate(ids[k]));actual[rows]={'rows':list(rows),'inactive':inactive[k].tolist(),'remaining_columns':left[k].tolist(),'diagonal_parity':parity[k].tolist()};context.append({'rows':list(rows),'T':T[k].tolist(),'R':R.tolist()})
  theirs={tuple(x['rows']):x for x in saved['survivors']};assert len(theirs)==len(saved['survivors']) and theirs==actual
  contexts[str(source['root'])]=context;out.append({'root':source['root'],'products':N,'flow':int(flow.sum()),'survivors':len(actual)})
 status='COMPLETE'
except TimeoutError:pass
result={'status':status,'original_cap_seconds':30,'seconds':time.monotonic()-start,'hashes':hashes,'premises':states,'records':out};(p/'results.json').write_text(json.dumps(result,indent=2)+'\n');(p/'contexts.json').write_text(json.dumps(contexts)+'\n');print(json.dumps({'status':status,'seconds':result['seconds'],'hashes':len(hashes),'cases':len(out),'products':sum(x['products'] for x in out),'flow':sum(x['flow'] for x in out),'survivors':sum(x['survivors'] for x in out)}))
