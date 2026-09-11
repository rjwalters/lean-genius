from pathlib import Path
import json,itertools as it,time
start=time.monotonic();p=Path(__file__).resolve().parent;rs=json.loads((p/'results.json').read_text())['records'];types={}
trans=[tuple(2*(perm+(3,4))[i]+(b^flip[i]) for i in range(5) for b in range(2)) for perm in it.permutations(range(3)) for flip in it.product(range(2),repeat=5)]
for r in rs:
 if time.monotonic()-start>30:raise TimeoutError('Original30s postprocessing cap exceeded')
 key=min(tuple(sorted(tuple(sorted((t[a],t[b]))) for a,b in r['edges'])) for t in trans)
 types.setdefault(key,[]).append(r)
classes=[]
for key,group in sorted(types.items()):
 r=next(r for r in rs if tuple(map(tuple,r['edges']))==key)
 classes.append({'representative_edges':key,'labelled_count':len(group),'support_orbits':r['supports']})
assert len(classes)==4 and sum(c['labelled_count'] for c in classes)==144
res={'status':'COMPLETE','original_postprocessing_cap_seconds':30,'seconds':time.monotonic()-start,'equivariant_maps':len(trans),'classes':classes}
(p/'classes.json').write_text(json.dumps(res,indent=2)+'\n');print(json.dumps({'classes':4,'counts':[c['labelled_count'] for c in classes],'seconds':res['seconds']}))
