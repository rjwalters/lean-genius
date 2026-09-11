from pathlib import Path
import json,itertools as it,time
p=Path(__file__).resolve().parent;b=p.parent;start=time.monotonic();a=json.loads((b/'residual-ten-D5-five-311-allocation/results.json').read_text())['records'];pack=json.loads((b/'residual-ten-D5-five-311-packing/results.json').read_text())['records'];dom=json.loads((b/'residual-ten-D5-supports/results.json').read_text())['records'];out=[]
def guard():
 if time.monotonic()-start>=30:raise TimeoutError
for ci in [5,6,7]:
 c=dom[ci];E={tuple(e) for e in c['edges']};autos=[]
 for perm in it.permutations(range(5)):
  for flips in it.product((0,1),repeat=5):
   guard();f=[2*perm[i]+(t^flips[i]) for i in range(5) for t in [0,1]]
   if {tuple(sorted((f[u],f[v]))) for u,v in E}==E:autos.append(f)
 lookup={tuple(s):i for i,s in enumerate(c['high3'])}
 def normalize(s):return min(tuple(sorted(s)),tuple(sorted(v^1 for v in s)))
 actions=[[lookup[normalize([f[v] for v in s])] for s in c['high3']] for f in autos]
 roots=[r for r in a if r['class']==ci and r['status']=='EXACT_RATIONAL_WITNESS'];bykey={tuple(pack[ci]['survivors'][r['source_root']]['high3']):r for r in roots};assert len(bykey)==len(roots);covered=set();orbits=[]
 for key,source in bykey.items():
  if key in covered:continue
  witnesses={}
  for ai,action in enumerate(actions):
   guard();target=tuple(sorted(action[j] for j in key));assert target in bykey
   if target not in witnesses:witnesses[target]=ai
  assert not covered&set(witnesses);covered.update(witnesses)
  members=[]
  for target,ai in sorted(witnesses.items()):
   r=bykey[target];f=autos[ai];q=pack[ci]['survivors'][source['source_root']]['q'];tq=pack[ci]['survivors'][r['source_root']]['q'];assert all(tq[f[e]]==q[e] for e in range(10))
   members.append({'root':r['root'],'source_root':r['source_root'],'automorphism':ai})
  orbits.append({'representative_root':source['root'],'representative_source_root':source['source_root'],'members':members})
 assert covered==set(bykey);out.append({'class':ci,'automorphisms':autos,'support_actions':actions,'orbits':orbits})
r={'status':'COMPLETE','original_cap_seconds':30,'seconds':time.monotonic()-start,'records':out};(p/'results.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'status':r['status'],'seconds':r['seconds'],'classes':[{'class':r['class'],'automorphisms':len(r['automorphisms']),'orbit_sizes':[len(o['members']) for o in r['orbits']]} for r in out]}))
