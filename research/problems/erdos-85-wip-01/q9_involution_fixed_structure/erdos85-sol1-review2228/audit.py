from pathlib import Path
import itertools,json,hashlib,time
p=Path(__file__).parent;src=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/q9-involution-four-orbit-cover');start=time.monotonic()
pins=json.loads((src/'pins.json').read_text())
for f,h in pins.items():assert hashlib.sha256((src/f).read_bytes()).hexdigest()==h
saved=json.loads((src/'matrices.json').read_text());byflat={tuple(x for r in z['Q'] for x in r):z for z in saved};assert len(byflat)==len(saved)
perms=list(itertools.permutations(range(4)));pairs=list(itertools.combinations(range(4),2));seen=set();classes={};allocs=0;symmetric=0
for bits in itertools.product(range(16),repeat=4):
 assert time.monotonic()-start<60
 Q=[[(bits[i]>>j)&1 for j in range(4)] for i in range(4)]
 if any(Q[i][j]!=Q[j][i] for i,j in pairs):continue
 symmetric+=1;Ac=4+sum(map(sum,Q))
 if Ac>10 or any(Q[i][i] and Q[j][j] and Q[i][j] for i,j in pairs):continue
 capacities=[2-(bits[i]&bits[j]).bit_count() for i,j in pairs]
 if min(capacities)<0:continue
 cv={c for c in itertools.product(range(3),repeat=6) if sum(c)==10-Ac and all(v<=cap for v,cap in zip(c,capacities))}
 if not cv:continue
 flat=tuple(x for r in Q for x in r);assert flat in byflat;z=byflat[flat];seen.add(flat)
 assert z['A_count']==Ac and z['missing_counts']==[1+sum(row) for row in Q] and z['pair_capacities']==capacities
 assert cv==set(map(tuple,z['repeat_allocations'])) and len(cv)==len(z['repeat_allocations']);allocs+=len(cv)
 canon=min(tuple(Q[t[i]][t[j]] for i in range(4) for j in range(4)) for t in perms)
 classes.setdefault(canon,set()).add(z['code'])
assert symmetric==1024 and seen==byflat.keys()
expected={tuple(x['canonical_flat']):set(x['codes']) for x in json.loads((src/'orbits.json').read_text())};assert classes==expected
res={'status':'PASS','all_symmetric_inputs':symmetric,'retained':len(seen),'classes':len(classes),'allocations':allocs,'seconds':time.monotonic()-start,'method':'all4-row bitpatterns, independent bitwise common counts, six unrestricted ternary allocation coordinates, direct24 relabellings'}
(p/'results.json').write_text(json.dumps(res,indent=2)+'\n');(p/'source-pins.json').write_text(json.dumps(pins,indent=2)+'\n');print(json.dumps(res))
