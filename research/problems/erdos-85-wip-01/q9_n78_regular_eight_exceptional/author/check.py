from pathlib import Path
import itertools,json,collections
p=Path(__file__).parent;edges=list(itertools.combinations(range(4),2));counts=collections.Counter();w=[]
for mask in range(64):
 G=[set() for _ in range(4)]
 for k,(i,j) in enumerate(edges):
  if mask>>k&1:G[i].add(j);G[j].add(i)
 deg=sorted(map(len,G))
 if deg[0]==0 or any(len(G[i]&G[j])>1 for i,j in edges):continue
 aut=[a for a in itertools.permutations(range(4)) if all({a[j] for j in G[i]}==G[a[i]] for i in range(4))]
 kind={ (1,1,1,1):'matching',(1,1,2,2):'path',(1,1,1,3):'star',(1,2,2,3):'triangle_pendant'}[tuple(deg)]
 n=len(aut);twopart=n&-n
 assert kind=='matching' or twopart<=2
 counts[kind]+=1;w.append({'mask':mask,'type':kind,'automorphisms':len(aut),'two_part':twopart})
assert dict(counts)=={'matching':3,'path':12,'star':4,'triangle_pendant':12}
(p/'results.json').write_text(json.dumps({'all_masks':64,'survivors':31,'types':dict(counts),'cases':w},indent=2)+'\n')
print('PASS all64 masks;31 relevant graphs; allnonmatching automorphism2parts<=2')
