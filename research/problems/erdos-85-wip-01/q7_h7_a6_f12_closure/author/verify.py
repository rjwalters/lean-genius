"""Independently reconstruct families and verify complete choice trees."""
import gzip,hashlib,itertools,json,time
from pathlib import Path
D=Path(__file__).parent;T=Path('/Users/rwalters/lean-genius-h7-a6-f12-weighted-family-sol2-20260915')
R=Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration/research/problems/erdos-85-wip-01');S=R/'q7_h7_a6_f12_host/original'
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def families(g):
 high=set(range(7));out={}
 for p in range(21,42):
  demand=7-2*len(g[p]);assert demand in [1,3]
  candidates=[s for s in range(7,21) if all(g[s].isdisjoint(g[w]) for w in g[p])];rows=[]
  for chosen in itertools.combinations(candidates,demand):
   if any(not g[a].isdisjoint(g[b]) for a,b in itertools.combinations(chosen,2)):continue
   covered=set().union(*(g[s]&high for s in chosen));assert len(covered)==demand;left=high-covered
   supports={frozenset(g[q]&high) for q in range(21,42) if q!=p and (g[q]&high)<=left and all(g[q].isdisjoint(g[w]) for w in g[p]|set(chosen))}
   if any(all(frozenset(order[i:i+2]) in supports for i in range(0,len(order),2)) for order in itertools.permutations(sorted(left))):rows.append(sum(1<<(s-7) for s in chosen))
  out[p]=rows
 return out

def main():
 for base in [T,S]:
  for n,h in read(base/'pins.json').items():assert sha(base/n)==h,n
 l=read(D/'launch.json');assert sha(D/'probe.py')==l['driver'] and sha(T/'pins.json')==l['source_manifest'] and sha(S/'pins.json')==l['host_manifest']
 r=read(D/'results.json');expected=list(map(tuple,read(T/'results.json')['remaining']));keys=[(c['global_index'],c['leaf_index']) for c in r['records']]
 assert keys+list(map(tuple,r['unvisited']))==expected and len(expected)==23
 ids={gid for gid,j in keys};inputs={a['global_index']:a for a in map(json.loads,gzip.open(S/'inputs.jsonl.gz','rt')) if a['global_index'] in ids};hosts={}
 for name in read(S/'results.json')['shards']:
  for a in map(json.loads,gzip.open(S/name,'rt')):
   if a['global_index'] in ids:hosts[a['global_index']]=a['receipt']
 start=time.monotonic();counts={s:0 for s in ['INFEASIBLE_PROJECTION','FEASIBLE_PROJECTION','UNKNOWN']};total_nodes=total_branches=0
 for rec in r['records']:
  assert time.monotonic()-start<60
  gid,j=rec['global_index'],rec['leaf_index'];g=[set(ns) for ns in inputs[gid]['neighbors']]
  for e,m in zip(hosts[gid]['empty_vertices'],hosts[gid]['solutions'][j]):
   for v in range(49):
    if m>>v&1:g[e].add(v);g[v].add(e)
  fs=families(g);assert {str(p):rows for p,rows in fs.items()}==rec['families'];cap=[7-len(g[s]) for s in range(7,21)];assert cap==rec['capacity']
  order=rec['order'];assert order==sorted(fs,key=lambda p:(len(fs[p]),p));st=rec['status'];counts[st]+=1
  if st=='UNKNOWN':assert rec['tree'] is None and rec['witness'] is None;continue
  if st=='FEASIBLE_PROJECTION':
   chosen={int(p):f for p,f in rec['witness'].items()};assert set(chosen)==set(fs) and all(f in fs[p] for p,f in chosen.items())
   assert [sum(bool(f>>s&1) for f in chosen.values()) for s in range(14)]==cap
   for p,f in chosen.items():
    for s in range(7,21):
     if f>>(s-7)&1:g[p].add(s);g[s].add(p)
   assert all(len(g[u]&g[v])<=1 for u in range(49) for v in range(u))
   assert all(len(g[s])==7 for s in range(7,21));continue
  assert st=='INFEASIBLE_PROJECTION' and rec['witness'] is None
  tree=rec['tree'];seen=set();assigned={};used=[0]*14
  def visit(index,depth):
   nonlocal total_nodes,total_branches
   assert time.monotonic()-start<60 and index not in seen and 0<=index<len(tree);seen.add(index);total_nodes+=1
   node=tree[index];assert node['depth']==depth and depth<len(order) and 'witness' not in node
   p=order[depth];branches=node['branches'];assert [b['family'] for b in branches]==list(range(len(fs[p])))
   for b in branches:
    total_branches+=1;f=fs[p][b['family']];ss=[s for s in range(14) if f>>s&1]
    if 'capacity_reject' in b:s=b['capacity_reject'];assert s in ss and used[s]>=cap[s]
    elif 'common_neighbour_reject' in b:
     q=b['common_neighbour_reject'];assert q in assigned and (f&assigned[q]).bit_count()+len(g[p]&g[q])>1
    else:
     assert set(b)=={'family','child'} and all(used[s]<cap[s] for s in ss) and all((f&h).bit_count()+len(g[p]&g[q])<=1 for q,h in assigned.items())
     assigned[p]=f
     for s in ss:used[s]+=1
     visit(b['child'],depth+1)
     for s in ss:used[s]-=1
     del assigned[p]
  visit(0,0);assert len(seen)==len(tree)==rec['nodes']<=10000
 assert counts==r['counts']
 out={'status':'PASS_PROJECTION_RECORDS','counts':counts,'checked_tree_nodes':total_nodes,'checked_branches':total_branches,'unvisited':r['unvisited'],'seconds':time.monotonic()-start,'scope':'Complete necessary families and every negative tree branch checked; positive projections omit P-P edges, UNKNOWN/unvisited preserved.'}
 (D/'verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
if __name__=='__main__':main()
