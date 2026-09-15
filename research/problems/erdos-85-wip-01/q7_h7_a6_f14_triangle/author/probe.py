"""New triangle-only necessary cut on the frozen F14 unfinished suffix.
Precompute fixed H/S compatibility per input; no residual row/ARC API.
"""
import gzip,hashlib,itertools,json,sqlite3,time
from pathlib import Path
P=Path(__file__).parent;B=Path('/Users/rwalters/lean-genius-h7-a6-f14-sol1-20260915');S=B/'hosts';F=B/'residual'
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert not (P/'launch.json').exists(),'No overwrite/restart'
for n,h in read(B/'host-pins.json').items():assert sha(B/n)==h
old=read(F/'results.json');assert old['stop']=='ARTIFACT_CAP' and old['visited']==1757882 and old['unvisited']==520726 and old['retained']==[]
allkeys=read(S/'survivors.json');assert len(allkeys)==2278608 and read(F/'input-survivors.json')==allkeys
queue=allkeys[old['visited']:];assert len(queue)==520726;wanted={gid for gid,j in queue}
inputs={}
for line in gzip.open(B/'inputs.jsonl.gz','rt'):
 r=json.loads(line)
 if r['global_index'] in wanted:inputs[r['global_index']]=[sum(1<<v for v in ns) for ns in r['neighbors']]
c=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True);reviews={}
for rid in [2705,2707]:
 st,res=c.execute('select status,resolution from review_requests where id=?',(rid,)).fetchone();assert st=='resolved' and res.startswith('PASS');reviews[rid]=res
pins={str(F/'results.json'):sha(F/'results.json'),str(F/'launch.json'):sha(F/'launch.json'),str(S/'survivors.json'):sha(S/'survivors.json'),str(B/'host-pins.json'):sha(B/'host-pins.json')}
(P/'launch.json').write_text(json.dumps({'seconds':120,'artifact_bytes':50000000,'cases':len(queue),'input_hashes':pins,'driver':sha(Path(__file__)),'reviews':reviews,'scope':'Host source reviewed; prefix count selects a domain only, prefix exclusions await review.'},indent=2)+'\n')
start=time.monotonic();negative=[];remaining=[];bad_masks={};position=0;visited=0;stop=None
# g[H] and g[S] do not change when adding E-P host edges.
def bad_pairs(g):
 compat=[0]*14
 for a,b in itertools.combinations(range(14),2):
  if not g[a+7]&g[b+7]:compat[a]|=1<<b;compat[b]|=1<<a
 bad=0
 for u in range(21,42):
  assert g[u].bit_count()==2 and g[u]&127==g[u]
  old=[h for h in range(7) if g[u]>>h&1];blocked=g[old[0]]|g[old[1]]
  cand=sum(1<<s for s in range(14) if not g[s+7]&blocked)
  triangle=False;vs=cand
  while vs and not triangle:
   bit=vs&-vs;v=bit.bit_length()-1;vs-=bit;ns=compat[v]&vs
   while ns:
    b=ns&-ns;w=b.bit_length()-1;ns-=b
    if compat[w]&compat[v]&vs:triangle=True;break
  if not triangle:bad|=1<<u
 return bad
for name in read(S/'results.json')['shards']:
 for line in gzip.open(S/name,'rt'):
  r=json.loads(line);gid=r['global_index'];hs=r['receipt']['solutions'];assert r['receipt']['status']=='COMPLETE'
  if position+len(hs)<=old['visited']:position+=len(hs);continue
  if time.monotonic()-start>=120:stop='AGGREGATE_CAP';break
  bad=bad_pairs(inputs[gid]);bad_masks[gid]=bad
  for j,masks in enumerate(hs):
   position+=1
   if position<=old['visited']:continue
   if time.monotonic()-start>=120:stop='AGGREGATE_CAP';break
   assert queue[visited]==[gid,j]
   occupied=0
   for m in masks:occupied|=m
   witness=bad&~occupied
   if witness:negative.append([gid,j,(witness&-witness).bit_length()-1])
   else:remaining.append([gid,j])
   visited+=1
  if stop:break
 if stop:break
unvisited=queue[visited:]
result={'status':'COMPLETE_PROBE' if not stop else 'CAPPED_PROBE','total':len(queue),'visited':visited,'negative':len(negative),'certificates':negative,'remaining':remaining,'unvisited':unvisited,'bad_pair_masks':bad_masks,'seconds':time.monotonic()-start,'stop':stop,'scope':'New triangle obstruction only. No row/ARC search or prefix promotion; unclassified/unvisited remain open.'}
blob=json.dumps(result,separators=(',',':')).encode();assert len(blob)<50000000
(P/'results.json').write_bytes(blob+b'\n')
for n,h in pins.items():assert sha(Path(n))==h
print({k:v for k,v in result.items() if k not in ['certificates','remaining','unvisited','bad_pair_masks']})
