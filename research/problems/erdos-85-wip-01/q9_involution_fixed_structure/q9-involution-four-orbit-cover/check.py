from pathlib import Path
import itertools,json,time,collections
p=Path(__file__).resolve().parent;start=time.monotonic();positions=[(i,j) for i in range(4) for j in range(i,4)];pairs=list(itertools.combinations(range(4),2));kept=[]
for code in range(1024):
 assert time.monotonic()-start<60
 Q=[[0]*4 for _ in range(4)]
 for k,(i,j) in enumerate(positions):Q[i][j]=Q[j][i]=(code>>k)&1
 A=4+sum(map(sum,Q))
 if A>10:continue
 if any(Q[i][i] and Q[j][j] and Q[i][j] for i,j in pairs):continue
 S=[[sum(Q[i][k]*Q[k][j] for k in range(4)) for j in range(4)] for i in range(4)]
 cap=[2-S[i][j] for i,j in pairs]
 if min(cap)<0 or sum(cap)<10-A:continue
 # Save every possible aggregate repeated-label distribution.
 allocations=[c for c in itertools.product(*(range(x+1) for x in cap)) if sum(c)==10-A]
 assert allocations
 kept.append({'code':code,'Q':Q,'A_count':A,'missing_counts':[1+sum(row) for row in Q],'pair_capacities':cap,'repeat_allocations':[list(c) for c in allocations]})
def canonical(Q):return min(tuple(Q[g[i]][g[j]] for i in range(4) for j in range(4)) for g in itertools.permutations(range(4)))
classes={}
for r in kept:classes.setdefault(canonical(r['Q']),[]).append(r['code'])
out={'status':'COMPLETE','original_wall_cap_seconds':60,'seconds':time.monotonic()-start,'inputs':1024,'retained':len(kept),'symmetry_classes':len(classes),'A_count_histogram':dict(collections.Counter(r['A_count'] for r in kept)),'allocation_count':sum(len(r['repeat_allocations']) for r in kept)}
(p/'matrices.json').write_text(json.dumps(kept,indent=2)+'\n');(p/'orbits.json').write_text(json.dumps([{'canonical_flat':list(k),'codes':v} for k,v in classes.items()],indent=2)+'\n');(p/'results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
