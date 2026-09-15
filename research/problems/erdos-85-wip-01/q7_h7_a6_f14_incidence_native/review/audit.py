"""Independent family and complete branch audit of the frozen native fixtures."""
import ctypes,hashlib,json,time
from pathlib import Path
from families import reconstruct
D=Path(__file__).parent
P=Path('/Users/rwalters/lean-genius-h7-a6-f14-incidence-native-sol2-20260915')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 pins={n:sha(P/n) for n in ['projection.cpp','projection.dylib','fixtures.json','qualification.json']}
 lib=ctypes.CDLL(str(P/'projection.dylib'));U=ctypes.c_uint64
 lib.check_projection.argtypes=[ctypes.POINTER(U),ctypes.c_int,ctypes.c_double];lib.check_projection.restype=ctypes.c_char_p
 start=time.monotonic();counts={};nodes=branches=0
 for fixture in json.loads((P/'fixtures.json').read_text()):
  assert time.monotonic()-start<60
  graph=fixture['graph'];g=[set(v for v in range(49) if mask>>v&1) for mask in graph]
  families,capacity=reconstruct(graph)
  cert=json.loads(lib.check_projection((U*49)(*graph),10000,time.monotonic()+2))
  status=cert['status'];counts[status]=counts.get(status,0)+1
  if status=='EMPTY_FAMILY':
   assert cert['pair_vertex'] in families and not families[cert['pair_vertex']]
   continue
  assert status in ['INFEASIBLE_PROJECTION','FEASIBLE_PROJECTION']
  saved={int(u):[frozenset(s+7 for s in range(14) if mask>>s&1) for mask in masks] for u,masks in cert['families'].items()}
  assert set(saved)==set(families)
  assert all(len(saved[u])==len(set(saved[u])) and set(saved[u])==set(families[u]) for u in families)
  assert cert['capacity']==[capacity[s] for s in range(7,21)]
  if status=='FEASIBLE_PROJECTION':
   chosen={int(u):frozenset(s+7 for s in range(14) if mask>>s&1) for u,mask in cert['witness'].items()}
   assert set(chosen)==set(families) and all(chosen[u] in families[u] for u in families)
   assert all(sum(s in f for f in chosen.values())==capacity[s] for s in capacity)
   assert all(len(chosen[u]&chosen[v])+len(g[u]&g[v])<=1 for u in chosen for v in chosen if u<v)
   continue
  order=cert['order'];assert len(order)==21 and set(order)==set(saved)
  tree=cert['tree'];seen=set()
  def visit(index,depth,chosen,usage):
   nonlocal nodes,branches
   assert time.monotonic()-start<60 and 0<=index<len(tree) and index not in seen and depth<21
   seen.add(index);nodes+=1;node=tree[index];assert node['depth']==depth
   u=order[depth];bs=node['branches'];assert [b['family'] for b in bs]==list(range(len(saved[u])))
   for b in bs:
    branches+=1;f=saved[u][b['family']]
    if 'capacity_reject' in b:
     s=b['capacity_reject']+7;assert s in f and usage.get(s,0)>=capacity[s]
    elif 'common_neighbour_reject' in b:
     v=b['common_neighbour_reject'];assert v in chosen and len(f&chosen[v])+len(g[u]&g[v])>1
    else:
     assert set(b)=={'family','child'}
     assert all(usage.get(s,0)<capacity[s] for s in f)
     assert all(len(f&h)+len(g[u]&g[v])<=1 for v,h in chosen.items())
     nxt=usage.copy()
     for s in f:nxt[s]=nxt.get(s,0)+1
     visit(b['child'],depth+1,chosen|{u:f},nxt)
  visit(0,0,{},{});assert len(seen)==len(tree)==cert['nodes']<=10000
 for n,h in pins.items():assert sha(P/n)==h
 out={'status':'PASS_INDEPENDENT_NATIVE_FIXTURES','counts':counts,'tree_nodes':nodes,'tree_branches':branches,'seconds':time.monotonic()-start,'input_hashes':pins,'scope':'Necessary families and every returned negative fixture certificate. Source fixture membership and native validation/caps reviewed separately. Positive path only checked if returned.'}
 (D/'REVIEW.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
if __name__=='__main__':main()
