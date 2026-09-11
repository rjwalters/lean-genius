from pathlib import Path
import itertools,json,hashlib,time
start=time.monotonic();src=Path('/Users/rwalters/lean-genius-q9-known-values-20260911/n78-kernel-two-cayley');out=Path(__file__).resolve().parent
pins={}
for n,h in json.loads((src/'pins.json').read_text()).items():
 p=src/n;assert hashlib.sha256(p.read_bytes()).hexdigest()==h;pins[str(p)]=h
prem=json.loads((src/'premise.json').read_text());assert hashlib.sha256(Path(prem['source']).read_bytes()).hexdigest()==prem['sha256'];pins[prem['source']]=prem['sha256']
for r in json.loads((out/'premise-states.json').read_text()):assert r['status']=='resolved' and r['resolution'].startswith('PASS')
saved=json.loads((src/'group.json').read_text());P=list(itertools.permutations(range(4)));ix={p:i for i,p in enumerate(P)}
def mul(p,q):return tuple(p[q[i]] for i in range(4))
T=[[ix[mul(p,q)] for q in P] for p in P];invs=[next(j for j in range(24) if T[j][i]==0) for i in range(24)]
r=ix[(1,2,3,0)];C={0,r,T[r][r],T[T[r][r]][r]}
cosets={frozenset(T[g][h] for h in C) for g in range(24)}
N={g for g in range(24) if {T[T[g][h]][invs[g]] for h in C}==C}
assert set(saved['C4'])==C and set(saved['normalizer'])==N
assert cosets==set(map(frozenset,saved['cosets'])) and len(cosets)==6
assert set(saved['cosets'][0])==C and set(saved['cosets'][1])==N-C
labels=[next(f for f,cs in enumerate(saved['cosets']) if i//2 in cs) for i in range(48)]
M=[[2*T[i//2][j//2]+((i%2)^(j%2)) for j in range(48)] for i in range(48)]
assert M==saved['multiplication'] and labels==saved['center_labels']
inv=[2*invs[i//2]+i%2 for i in range(48)]
# Enumerate inverse-closed sets from exact covers by inversion orbits.
allowed=[0,2,3,4,5];bits={f:1<<j for j,f in enumerate(allowed)};atoms=[]
for x in range(1,48):
 if inv[x]<x:continue
 a=tuple(sorted({x,inv[x]}));fs=[labels[z] for z in a]
 if len(set(fs))==len(fs) and all(f in bits for f in fs):atoms.append((sum(bits[f] for f in fs),a))
def visit(mask,chosen):
 if mask==31:yield tuple(sorted(chosen));return
 bit=next(1<<j for j in range(5) if not(mask&(1<<j)))
 for m,a in atoms:
  if m&bit and not m&mask:yield from visit(mask|m,chosen+a)
domain=set(visit(0,()));cert=json.loads((src/'certificates.json').read_text());assert len(domain)==len(cert)==228 and domain=={tuple(sorted(c['S'])) for c in cert}
edges=0
for c in cert:
 S=set(c['S']);adj=[set() for _ in range(54)]
 def edge(x,y):assert x!=y;adj[x].add(y);adj[y].add(x)
 # Matching inferred from translating the normalizer partner under G.
 for g in range(48):
  a=labels[g];b=labels[M[g][2*next(iter(N-C))]];edge(a,b)
  edge(6+g,a)
  for s in S:edge(6+g,6+M[g][s])
 assert [len(a) for a in adj]==[9]*6+[6]*48
 cyc=c['cycle'];assert len(cyc)==len(set(cyc))==4
 for x,y in zip(cyc,cyc[1:]+cyc[:1]):assert y in adj[x];edges+=1
# Normal-form table checked in S4 only as a sanity check, not an extension proof.
a=ix[(1,0,2,3)];b=ix[(0,2,1,3)];c=ix[(0,1,3,2)]
U={0,a,b,T[a][b],T[b][a],T[T[a][b]][a]};reps=[0,c,T[c][b],T[T[c][b]][a]]
assert len({T[u][v] for u in U for v in reps})==24
result={'status':'COMPLETE','original_audit_cap_seconds':30,'seconds':time.monotonic()-start,'group_products':48*48,'center_cosets':6,'inverse_closed_sets':len(domain),'certificate_edges':edges,'survivors':0,'premises':[2264,2268,2306]}
assert result['seconds']<30
(out/'input-pins.json').write_text(json.dumps(pins,indent=2)+'\n');(out/'verification.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
