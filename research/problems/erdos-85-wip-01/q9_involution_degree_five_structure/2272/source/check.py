import itertools,json
from pathlib import Path
ROOT=Path(__file__).resolve().parent

def run():
 result=[]
 for index,graph in enumerate(json.loads((ROOT/'representatives.json').read_text())):
  H=[set() for _ in range(10)]
  for a,b in graph['edges']:H[a].add(b);H[b].add(a)
  assert all(len(row)==3 for row in H)
  assert all(len(H[a]&H[b])<=1 for a,b in itertools.combinations(range(10),2))
  for P0 in itertools.combinations(range(10),4):
   P=set(P0);M=set(range(10))-P;d=[len(row&P) for row in H]
   if min(d)<1 or any(d[f]>2 for f in M):continue
   kind='star' if max(d)==3 else 'matching_path'
   if kind=='star':assert sorted(d[f] for f in P)==[1,1,1,3]
   else:
    assert all(d[f]==1 for f in P)
    assert sorted(len(H[f]&M) for f in M)==[1,1,2,2,2,2]
    seen=set();stack=[min(M)]
    while stack:
     u=stack.pop()
     if u in seen:continue
     seen.add(u);stack.extend((H[u]&M)-seen)
    assert seen==M
   result.append(dict(graph_index=index,P=list(P0),kind=kind,degree_P=d))
 assert len(result)==24
 assert sum(r['kind']=='star' for r in result)==15
 assert sum(r['kind']=='matching_path' for r in result)==9
 return dict(marked_pairs_checked=630,retained=result)
if __name__=='__main__':print(json.dumps(run(),indent=2))
