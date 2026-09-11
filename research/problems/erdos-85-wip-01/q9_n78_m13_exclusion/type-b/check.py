from pathlib import Path
import itertools,json
p=Path(__file__).parent
fold=lambda x:min(x%13,(-x)%13)
table=[]
for t in range(2,7):
 f={fold(2),fold(2*t),fold(1+t),fold(1-t)};remaining=set(range(1,7))-f
 valid=[]
 for ss in itertools.combinations(sorted(remaining),3):
  if any(sum(a*b for a,b in zip(ss,signs))%13==0 for signs in itertools.product([-1,1],repeat=3)):valid.append(ss)
 assert not valid
 table.append({'t':t,'forbidden':sorted(f),'remaining':sorted(remaining),'valid_signed_zero_triples':valid})
# Independent direct check of every actual offset triple for each normalized t.
counts={}
for t in range(1,7):
 count=0
 for T in itertools.combinations(range(13),3):
  adjacency=[set() for _ in range(26)]
  def edge(u,v):adjacency[u].add(v);adjacency[v].add(u)
  for x in range(13):
   edge(x,(x+1)%13);edge(13+x,13+(x+t)%13)
   for u in T:edge(x,13+(x+u)%13)
  has_c4=any(len(adjacency[i]&adjacency[j])>=2 for i in range(26) for j in range(i+1,26))
  assert has_c4,(t,T)
  count+=1
 counts[t]=count
r={'status':'PASS','table':table,'direct_local_26_vertex_checks':counts,'scope':'Finite verification of the local two-orbit lemma; not enumeration of full78-vertex lifts'}
(p/'results.json').write_text(json.dumps(r,indent=2)+'\n');print(r)
