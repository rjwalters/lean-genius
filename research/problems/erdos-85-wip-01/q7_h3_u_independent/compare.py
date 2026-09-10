from pathlib import Path
from itertools import permutations
import json,time
import census
import argparse
parser=argparse.ArgumentParser();parser.add_argument('--data-dir',type=Path,required=True);parser.add_argument('--output',type=Path,required=True)
args=parser.parse_args();p=args.data_dir;independent=json.loads((p/'results.json').read_text());results=[]
expected_files={'production-4.json','production-5.json','production-m1r4-5.json','production-m2-4.json','production-m2-5.json'}
assert {f.name for f in p.glob('production-*.json')}==expected_files
assert len(independent)==2 and {r['cross_size'] for r in independent}=={4,5}
for production_path in sorted(p.glob('production-*.json')):
 production=json.loads(production_path.read_text())
 size=sum(j>=0 for j in production['representatives'][0]['permutation'])
 assert all(sum(j>=0 for j in row['permutation'])==size for row in production['representatives'])
 record=next(r for r in independent if r['cross_size']==size)
 lookup={tuple(row['adjacency']):row['orbit_size_in_fixed_A_universe'] for row in record['orbits']}
 joined=[];seen=set();started=time.monotonic()
 for idx,row in enumerate(production['representatives']):
  edges=[(i,5+i) for i in range(5)]+[(i,10+i) for i in range(5)]
  edges.extend((5+i,10+j) for i,j in enumerate(row['permutation']) if j>=0)
  edges.extend((5*b+i,5*b+j) for b,es in enumerate(row['matchings']) for i,j in es)
  a=census.adjacency(edges);assert census.valid(a)
  colors=list(permutations(range(3))) if size==5 else [(0,1,2),(0,2,1)]
  images=[]
  for color in colors:
   for order in permutations(range(5)):
    image=census.transport(a,color,order)
    if image is not None:images.append(image)
  key=min(images);assert key in lookup and key not in seen;seen.add(key)
  assert row['orbit_size']==15*lookup[key]
  joined.append({'production_index':idx,'independent_adjacency':key,'production_orbit_size':row['orbit_size'],'fixed_A_orbit_size':lookup[key]})
 assert seen==set(lookup)
 assert production['configs']==record['all_A_matching_survivors']
 results.append({'cross_size':size,'source':production['source'],'source_sha256':production['sha256'],
                 'status':'BIJECTION','matches':joined,'seconds':time.monotonic()-started})
 print(size,len(joined),'BIJECTION with all orbit sizes scaling by15',flush=True)
with args.output.open('x') as out:json.dump(results,out,indent=2);out.write('\n')
