from itertools import combinations, permutations
from collections import Counter
import json,time
from pathlib import Path

def matching_edges():
 out=[]
 for es in combinations(list(combinations(range(5),2)),2):
  if len(set(sum((list(e) for e in es),[])))==4:out.append(es)
 assert len(out)==15
 return out

def adjacency(edges):
 a=[0]*15
 for x,y in edges:a[x]|=1<<y;a[y]|=1<<x
 return tuple(a)

def valid(a):
 return all((a[i]&a[j]).bit_count()<2 for i in range(15) for j in range(i))

def transport(a,color_order,ordering):
 mapping={}
 for i,oldi in enumerate(ordering):
  x=5*color_order[0]+oldi
  bs=[v for v in range(5*color_order[1],5*color_order[1]+5) if a[x]>>v&1]
  cs=[v for v in range(5*color_order[2],5*color_order[2]+5) if a[x]>>v&1]
  assert len(bs)==len(cs)==1
  mapping[x]=i;mapping[bs[0]]=5+i;mapping[cs[0]]=10+i
 assert len(mapping)==15
 internal={(mapping[u],mapping[v]) if mapping[u]<mapping[v] else (mapping[v],mapping[u])
           for u in range(5*color_order[0],5*color_order[0]+5)
           for v in range(u+1,5*color_order[0]+5) if a[u]>>v&1}
 if internal!={(0,1),(2,3)}:return None
 return adjacency((mapping[i],mapping[j]) for i in range(15) for j in range(i) if a[i]>>j&1)

def census(size):
 start=time.monotonic();matchings=matching_edges();graphs=set();candidates=0
 maps=set()
 for domain in combinations(range(5),size):
  for image in permutations(range(5),size):maps.add(tuple(zip(domain,image)))
 for cross in sorted(maps):
  fixed=[(i,5+i) for i in range(5)]+[(i,10+i) for i in range(5)]+[(5+i,10+j) for i,j in cross]+[(0,1),(2,3)]
  for b in matchings:
   for c in matchings:
    candidates+=1
    a=adjacency(fixed+[(5+i,5+j) for i,j in b]+[(10+i,10+j) for i,j in c])
    if valid(a):graphs.add(a)
 all_orderings=list(permutations(range(5)))
 colors=list(permutations(range(3))) if size==5 else [(0,1,2),(0,2,1)]
 unseen=set(graphs);orbits=[]
 while unseen:
  a=min(unseen);orbit=set()
  for colorspec in colors:
   for ordering in all_orderings:
    image=transport(a,colorspec,ordering)
    if image is not None:orbit.add(image)
  assert orbit<=unseen
  unseen-=orbit
  orbits.append({'adjacency':a,'orbit_size_in_fixed_A_universe':len(orbit)})
 return {'cross_size':size,'bc_maps':len(maps),'candidates':candidates,
         'fixed_A_survivors':len(graphs),'all_A_matching_survivors':15*len(graphs),
         'orbits':orbits,'seconds':time.monotonic()-start}

if __name__=='__main__':
 import argparse
 parser=argparse.ArgumentParser();parser.add_argument('--output',type=Path,required=True)
 args=parser.parse_args()
 results=[]
 for n in [5,4]:
  r=census(n);results.append(r)
  print({k:v if k!='orbits' else len(v) for k,v in r.items()},flush=True)
 with args.output.open('x') as out:json.dump(results,out,indent=2);out.write('\n')
