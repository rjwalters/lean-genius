"""Coupled triangle-family subset capacities, without row/ARC generation."""
import gzip,hashlib,itertools,json,sqlite3,time
from pathlib import Path
D=Path(__file__).parent;T=Path('/Users/rwalters/lean-genius-h7-a6-f12-hall-capacity-sol2-20260915')
R=Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration/research/problems/erdos-85-wip-01');S=R/'q7_h7_a6_f12_host/original'
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def families(g):
 out={};capacity=[7-g[s].bit_count() for s in range(7,21)]
 for p in range(21,42):
  old=[w for w in range(49) if g[p]>>w&1];demand=7-2*g[p].bit_count();assert demand in [1,3]
  candidates=[s for s in range(7,21) if all(not(g[s]&g[w]) for w in old)]
  if demand==1:out[p]=[1<<(s-7) for s in candidates];continue
  fs=[]
  for tri in itertools.combinations(candidates,3):
   if any(g[a]&g[b] for a,b in itertools.combinations(tri,2)):continue
   used=0
   for s in tri:used|=g[s]&127
   assert used.bit_count()==3;left=127^used
   pairs=[q for q in range(21,42) if q!=p and not((g[q]&127)&~left) and all(not(g[q]&g[w]) for w in old+list(tri))]
   if any(not((g[a]&127)&(g[b]&127)) for a,b in itertools.combinations(pairs,2)):fs.append(sum(1<<(s-7) for s in tri))
  out[p]=fs
 assert all(out.values()) and sum(capacity)==39
 return out,capacity

def main():
 assert not (D/'launch.json').exists();db=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True);st,review=db.execute('select status,resolution from review_requests where id=2708').fetchone();assert st=='resolved' and review.startswith('PASS')
 for base in [T,S]:
  for n,h in read(base/'pins.json').items():assert sha(base/n)==h,n
 cases=read(T/'results.json')['remaining'];assert len(cases)==29;ids={gid for gid,j in cases}
 bases={r['global_index']:[sum(1<<v for v in ns) for ns in r['neighbors']] for r in map(json.loads,gzip.open(S/'inputs.jsonl.gz','rt')) if r['global_index'] in ids};hosts={}
 for name in read(S/'results.json')['shards']:
  for r in map(json.loads,gzip.open(S/name,'rt')):
   if r['global_index'] in ids:hosts[r['global_index']]=r['receipt']['solutions']
 (D/'launch.json').write_text(json.dumps({'seconds':60,'cases':29,'source_manifest':sha(T/'pins.json'),'host_manifest':sha(S/'pins.json'),'driver':sha(Path(__file__)),'review2708':review},indent=2)+'\n')
 start=time.monotonic();certs=[];remaining=[];tested=0;stop=None;unvisited=[]
 for index,(gid,j) in enumerate(cases):
  g=bases[gid][:]
  for e,m in enumerate(hosts[gid][j],42):
   g[e]|=m
   for v in range(49):
    if m>>v&1:g[v]|=1<<e
  fs,capacity=families(g);cut=None
  for mask in range(1,(1<<14)-1):
   if time.monotonic()-start>=60:stop='AGGREGATE_CAP';break
   actual=sum(c for s,c in enumerate(capacity) if mask>>s&1)
   lower=upper=0
   for rows in fs.values():
    counts=[(r&mask).bit_count() for r in rows];lower+=min(counts);upper+=max(counts)
   if not lower<=actual<=upper:cut={'singleton_mask':mask,'capacity':actual,'lower':lower,'upper':upper};break
  if stop:unvisited=cases[index:];break
  tested+=1
  if cut:cut.update(global_index=gid,leaf_index=j,families=fs);certs.append(cut)
  else:remaining.append([gid,j])
 out={'status':'COMPLETE_PROBE' if not stop else 'CAPPED_PROBE','total':29,'tested':tested,'killed':len(certs),'certificates':certs,'remaining':remaining,'unvisited':unvisited,'stop':stop,'seconds':time.monotonic()-start,'scope':'Necessary family subset capacity only; unclassified or unvisited cases preserved.'}
 (D/'results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k not in ['certificates','remaining','unvisited']}));print('remaining',len(remaining),'unvisited',len(unvisited))
if __name__=='__main__':main()
