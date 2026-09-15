"""Bounded exact singleton-pair incidence projection; no new pair-pair edges."""
import gzip,hashlib,importlib.util,json,sqlite3,time
from pathlib import Path
D=Path(__file__).parent;T=Path('/Users/rwalters/lean-genius-h7-a6-f12-weighted-family-sol2-20260915')
R=Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration/research/problems/erdos-85-wip-01');S=R/'q7_h7_a6_f12_host/original'
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
class Limit(Exception):pass

def solve(g,fs,capacity,deadline):
 order=sorted(fs,key=lambda p:(len(fs[p]),p));assigned={};used=[0]*14;tree=[];witness=None
 def visit(depth):
  nonlocal witness
  if time.monotonic()>deadline or len(tree)>=10000:raise Limit()
  index=len(tree);node={'depth':depth,'branches':[]};tree.append(node)
  if depth==len(order):
   assert used==capacity;witness=dict(assigned);node['witness']=True;return index,True
  p=order[depth]
  for i,f in enumerate(fs[p]):
   chosen=[s for s in range(14) if f>>s&1];over=next((s for s in chosen if used[s]>=capacity[s]),None)
   if over is not None:node['branches'].append({'family':i,'capacity_reject':over});continue
   conflict=next((q for q,h in assigned.items() if (f&h).bit_count()+(g[p]&g[q]).bit_count()>1),None)
   if conflict is not None:node['branches'].append({'family':i,'common_neighbour_reject':conflict});continue
   assigned[p]=f
   for s in chosen:used[s]+=1
   child,positive=visit(depth+1);node['branches'].append({'family':i,'child':child})
   for s in chosen:used[s]-=1
   del assigned[p]
   if positive:return index,True
  return index,False
 try:
  _,positive=visit(0)
  return {'status':'FEASIBLE_PROJECTION' if positive else 'INFEASIBLE_PROJECTION','order':order,'nodes':len(tree),'witness':witness,'tree':None if positive else tree}
 except Limit:return {'status':'UNKNOWN','order':order,'nodes':len(tree),'witness':None,'tree':None}

def main():
 assert not (D/'launch.json').exists();db=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True);st,review=db.execute('select status,resolution from review_requests where id=2712').fetchone();assert st=='resolved' and review.startswith('PASS')
 for base in [T,S]:
  for n,h in read(base/'pins.json').items():assert sha(base/n)==h,n
 sp=importlib.util.spec_from_file_location('refined_families',T/'probe.py');mod=importlib.util.module_from_spec(sp);sp.loader.exec_module(mod)
 cases=read(T/'results.json')['remaining'];assert len(cases)==23;ids={gid for gid,j in cases}
 bases={r['global_index']:[sum(1<<v for v in ns) for ns in r['neighbors']] for r in map(json.loads,gzip.open(S/'inputs.jsonl.gz','rt')) if r['global_index'] in ids};hosts={}
 for name in read(S/'results.json')['shards']:
  for r in map(json.loads,gzip.open(S/name,'rt')):
   if r['global_index'] in ids:hosts[r['global_index']]=r['receipt']['solutions']
 (D/'launch.json').write_text(json.dumps({'seconds':60,'nodes_per_case':10000,'artifact_bytes':50000000,'cases':23,'source_manifest':sha(T/'pins.json'),'host_manifest':sha(S/'pins.json'),'driver':sha(Path(__file__)),'review2712':review},indent=2)+'\n')
 start=time.monotonic();records=[];unvisited=[];size=0
 for index,(gid,j) in enumerate(cases):
  if time.monotonic()-start>=60:unvisited=cases[index:];break
  g=bases[gid][:]
  for e,m in enumerate(hosts[gid][j],42):
   g[e]|=m
   for v in range(49):
    if m>>v&1:g[v]|=1<<e
  fs,capacity=mod.families(g);result=solve(g,fs,capacity,start+60);result.update(global_index=gid,leaf_index=j,families=fs,capacity=capacity)
  n=len(json.dumps(result,separators=(',',':')).encode())
  if size+n>50000000:unvisited=cases[index:];break
  records.append(result);size+=n
 counts={st:sum(r['status']==st for r in records) for st in ['INFEASIBLE_PROJECTION','FEASIBLE_PROJECTION','UNKNOWN']}
 out={'status':'COMPLETE_PROBE' if not unvisited else 'CAPPED_PROBE','total':23,'counts':counts,'records':records,'unvisited':unvisited,'artifact_bytes':size,'seconds':time.monotonic()-start,'scope':'Necessary singleton-pair incidence projection only; feasible projections omit all missing pair-pair edges and are not graph witnesses.'}
 (D/'results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k not in ['records','unvisited']}))
if __name__=='__main__':main()
