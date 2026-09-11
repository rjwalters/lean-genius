"""One finite relabelling quotient of the accepted a6 high cover."""
import array,collections,gzip,hashlib,itertools,json,pathlib,sqlite3,sys,time
P=pathlib.Path(__file__).parent;A=pathlib.Path('/tmp/erdos85-sol1-h7-a6-projection-extension')
UNSET=2**32-1
def encode(c):return sum(h<<(3*d) for d,h in enumerate(c))
def transform(c,dp,cp):
 mins=[11]*7
 for d,h in enumerate(c):
  if h>=3:mins[h]=min(mins[h],dp[d])
 hp=list(cp)+[0]*4
 for h,old in enumerate(sorted(range(3,7),key=lambda h:mins[h]),3):hp[old]=h
 return sum(hp[h]<<(3*dp[d]) for d,h in enumerate(c))
def canon(es):return tuple(sorted(tuple(sorted(e)) for e in es))
class Limit(Exception):pass
def main():
 assert not (P/'launch.json').exists(),'No overwrite or retry'
 db=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True);db.row_factory=sqlite3.Row
 review=dict(db.execute('select * from review_requests where id=2122').fetchone());assert review['status']=='resolved' and review['resolution'].startswith('PASS')
 for f,h in json.loads((A/'pins.json').read_text()).items():assert hashlib.sha256((A/f).read_bytes()).hexdigest()==h
 cover=json.loads((A/'source-cover-results.json').read_text());comp=json.loads((A/'source-completion-results.json').read_text())
 records=[];groups=collections.defaultdict(list);layout=[];total=0
 with gzip.open(A/'high-colourings.jsonl.gz','rt') as stream:
  for line in stream:
   r=json.loads(line);assert r['status']=='COMPLETE';records.append(r);groups[r['completion_index']].append(r)
   r['global_start']=total;layout.append({k:r[k] for k in ['completion_index','singleton_index','F_index','X_index','global_start']}|dict(count=len(r['colourings'])))
   total+=len(r['colourings'])
 assert total==818836 and len(records)==3284
 (P/'premise.json').write_text(json.dumps(review,indent=2)+'\n');(P/'source-pins.json').write_bytes((A/'pins.json').read_bytes())
 (P/'launch.json').write_text(json.dumps(dict(total=total,seconds=60,max_operations_per_orbit=100000))+'\n')
 mapping=array.array('I',[UNSET])*(2*total);assert mapping.itemsize==4
 start=time.monotonic();actions={};aut={};reps=[];transforms=0;action_checks=0;complete=True
 def deadline():
  if time.monotonic()-start>60:raise Limit
 try:
  for ci,rs in groups.items():
   deadline();src=comp['results'][ci];F=cover['cases'][src['F_index']];X=F['representatives'][src['X_index']];hosts=X['singleton_hosts']
   if src['F_index'] not in aut:
    fs=canon(F['F_edges']);aa=[]
    for p in itertools.permutations(range(7)):
     action_checks+=1;deadline()
     if canon((p[a],p[b]) for a,b in fs)==fs:aa.append(p)
    aut[src['F_index']]=aa
   xs=canon(X['X_edges']);di={tuple(h):d for d,h in enumerate(hosts[:11])};sol={canon(es):j for j,es in enumerate(src['solutions'])};acts=[]
   for ep in aut[src['F_index']]:
    if canon((ep[a],ep[b]) for a,b in xs)!=xs:continue
    dp=[di[tuple(sorted(ep[e] for e in h))] for h in hosts[:11]]
    for cp in itertools.permutations(range(3)):
     if any(ep[hosts[11+k][0]]!=hosts[11+cp[k]][0] for k in range(3)):continue
     vp=list(ep)+[7+d for d in dp]+[18+c for c in cp]
     jm=[]
     for es in src['solutions']:
      action_checks+=1;deadline();jm.append(sol[canon((vp[a],vp[b]) for a,b in es)])
     acts.append(dict(E=list(ep),D=dp,C=list(cp),solutions=jm))
   assert 0<len(acts)<=100000
   actions[ci]=acts
   lookup={(r['singleton_index']<<33)|encode(c):r['global_start']+k for r in rs for k,c in enumerate(r['colourings'])}
   assert len(lookup)==sum(len(r['colourings']) for r in rs)
   for r in rs:
    j=r['singleton_index']
    for k,c in enumerate(r['colourings']):
     gid=r['global_start']+k
     if mapping[2*gid]!=UNSET:continue
     image={}
     for ai,a in enumerate(acts):
      deadline();transforms+=1
      key=(a['solutions'][j]<<33)|transform(c,a['D'],a['C']);member=lookup[key]
      assert mapping[2*member] in [UNSET,gid]
      image.setdefault(member,ai)
     # Commit only a complete orbit, never an interrupted image set.
     assert gid in image and min(image)==gid
     for member,ai in image.items():mapping[2*member]=gid;mapping[2*member+1]=ai
     reps.append(dict(global_index=gid,completion_index=ci,singleton_index=j,colouring_index=k,orbit_size=len(image)))
 except Limit:complete=False
 if sys.byteorder!='little':mapping.byteswap()
 (P/'orbit-map.u32le').write_bytes(mapping.tobytes())
 (P/'actions.json').write_text(json.dumps(actions,separators=(',',':'))+'\n');(P/'source-layout.json').write_text(json.dumps(layout,separators=(',',':'))+'\n');(P/'representatives.json').write_text(json.dumps(reps,separators=(',',':'))+'\n')
 covered=sum(r['orbit_size'] for r in reps)
 result=dict(status='COMPLETE' if complete else 'UNKNOWN',total=total,covered=covered,uncovered=total-covered,representatives=len(reps),transforms=transforms,action_checks=action_checks,seconds=time.monotonic()-start,orbit_histogram=dict(collections.Counter(r['orbit_size'] for r in reps)))
 (P/'results.json').write_text(json.dumps(result,indent=2)+'\n');print(result)
if __name__=='__main__':main()
