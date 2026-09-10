from pathlib import Path
import itertools,json,hashlib
root=Path(__file__).parent;src=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/review2026/core-t2.json');raw=src.read_bytes();C=json.loads(raw);assert C['masks']==[7,25,10,18,12,20]
open_cores=[44,1537,6145,9217,9729];adjacent=[x for x in open_cores if x&1];assert adjacent==[1537,6145,9217,9729] and set(open_cores)<=set(C['canonical_cores'])
W=set(range(10));UA=set(range(6));total=local=survive=0;ks=set()
for left in itertools.combinations(W,3):
 L=set(left)
 for right in itertools.combinations(W-L,3):
  R=set(right);total+=1
  if len(L-UA)>1 or len(R-UA)>1:continue
  local+=1;UB=L|R;k=len(UA&UB);ks.add(k)
  common=(W-UA)&(W-UB);assert len(common)==k-2 and k>=4
  if len(common)<=1:survive+=1
assert total==4200 and survive==0
out=dict(source_sha256=hashlib.sha256(raw).hexdigest(),adjacent_open_cores=adjacent,nonadjacent_open_core=44,ordered_disjoint_neighborhood_pairs=total,passing_special_common_neighbor_bounds=local,overlap_values=sorted(ks),passing_both_forced_empty_rows=survive,scope='Set-counting obstruction for every adjacent-triple T2 graph, conditional on reviewed premises; no capped graph search rerun')
(root/'result.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
