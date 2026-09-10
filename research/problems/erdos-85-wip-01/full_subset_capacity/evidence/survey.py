from pathlib import Path
import itertools,re,json,time,importlib.util,hashlib
p=Path(__file__).parent;private=p.parent;repo=Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration');start=time.monotonic()
f=repo/'research/problems/erdos-85-wip-01/low_degree_obstructions/count.py';spec=importlib.util.spec_from_file_location('u',f);u=importlib.util.module_from_spec(spec);spec.loader.exec_module(u)
s=(private/'u_full_restricted_shards/Full_3_3.lean').read_text();arrays=[list(map(int,re.search(r'def rep'+x+r'.*?!\[([^]]+)\]',s).group(1).split(','))) for x in ['A','B','P']]
s=(repo/'proofs/Proofs/Erdos85ThreeHighSecondaryOrbitTable.lean').read_text().split('private def orbitWitnesses')[0];codes=[(int(a),int(b),int(c),d=='true') for a,b,c,d in re.findall(r'threeHighSecondaryCode (\d+) (\d+) (\d+) (true|false)',s)];assert len(codes)==21
perms=list(itertools.permutations(range(5)));targets=[0,1,2,3,4,5,7,8,10,11,12,13,16,19,20,23,24,25,26,27,28,29,30,32,35,37,40,48,54]
farU={1,2,4,6,8,9,12,13,14,16,18,21,22,34};farR={3,6,8,10,12,13,20};degree6={0,1,2,4,5,7,9,11}
pairs=[(r,q) for r in targets if r not in {0,11,23,35} for q in range(21) if q not in degree6 and not (r in farU and q in farR) and (r,q)!=(1,14)];assert len(pairs)==275
candidates=[tuple(5*k+i for k,i in enumerate(t) if i>=0) for t in itertools.product(range(-1,5),repeat=3)]
def c4(E):return any((E[x]&E[y]).bit_count()>1 for x in range(24) for y in range(x))
def add(E,j,S):
 F=E.copy()
 for i in S:F[i]|=1<<(15+j);F[15+j]|=1<<i
 return F
capcache={};ucache={}
def capacities(D):
 key=tuple(sum(1<<i for i in S) for S in D)
 if key in capcache:return capcache[key]
 cap=bytearray(32768)
 for m in key:
  sub=m
  while sub:
   cap[sub]=sub.bit_count();sub=(sub-1)&m
 for bit in range(15):
  step=1<<bit
  for base in range(0,32768,step*2):
   for i in range(base,base+step):
    if cap[i]>cap[i+step]:cap[i+step]=cap[i]
 capcache[key]=cap;return cap
results=[]
for r,q in pairs:
 if time.monotonic()-start>120:break
 if r not in ucache:
  a,b,c=[x[r] for x in arrays];U=u.adjacency(u.MASKS[a],u.MASKS[b],perms[c],None);need=[4-x.bit_count() for x in U];dem=[0]*32768
  for m in range(1,32768):bit=m&-m;dem[m]=dem[m^bit]+need[bit.bit_length()-1]
  ucache[r]=(U,dem,[a,b,c])
 U,dem,compact=ucache[r];m,a,b,far=codes[q];R=[0]*8
 edges=[(2*i,2*i+1) for i in range(m+1)]+([(6,a-1)] if a else [])+([(7,b-1)] if b else [])+([(6,7)] if far else [])
 for x,y in edges:R[x]|=1<<y;R[y]|=1<<x
 assert sum(x.bit_count() for x in R)==8
 fixed=U+[x<<15 for x in R]+[0]
 for j in range(6):fixed[23]|=1<<(15+j);fixed[15+j]|=1<<23
 D=[[S for S in candidates if len(S)==4-R[j].bit_count()-(j<6) and not c4(add(fixed,j,S))] for j in range(8)]
 empty=next((j for j,d in enumerate(D) if not d),None)
 witness=None
 if empty is None:
  caps=[capacities(d) for d in D]
  for mask in range(32768):
   cs=[c[mask] for c in caps]
   if dem[mask]>sum(cs):witness={'mask':mask,'demand':dem[mask],'caps':cs};break
 row={'pair':[r,q],'compact':compact,'r_code':list(codes[q]),'domain_sizes':list(map(len,D)),'empty_column':empty,'witness':witness};results.append(row)
 if witness or empty is not None:print(json.dumps(row),flush=True)
 (p/'progress.json').write_text(json.dumps({'scope':'Python complete-domain subset-capacity proposal only; no Lean exclusion','elapsed_seconds':time.monotonic()-start,'checked_pairs':len(results),'total_pairs':275,'exhausted':len(results)==275,'results':results},indent=2)+'\n')
print('Finished',len(results),'pairs',time.monotonic()-start,'seconds',flush=True)
