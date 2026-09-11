from pathlib import Path
import itertools,json
p=Path(__file__).resolve().parent
ps=list(itertools.permutations(range(3)));pairs=list(itertools.combinations(range(5),2));out=[]
for r in map(json.loads,(p/'receipts.jsonl').read_text().splitlines()):
 P={}
 for (u,v),z in zip(pairs,r['example']):P[u,v]=ps[z];P[v,u]=tuple(ps[z].index(a) for a in range(3))
 words=[]
 for word in itertools.product(range(3),repeat=5):
  good=True
  for u,v in pairs:
   a,b=word[u],word[v];hits=0
   if a and P[u,v][3-a]==b:hits+=1
   if P[u,v][a] and 3-P[u,v][a]==b:hits+=1
   for w in range(5):
    if w not in (u,v) and P[w,v][P[u,w][a]]==b:hits+=1
   if hits>=3:good=False;break
  if good:words.append(word)
 counts=[[sum(w[u]==a for w in words) for a in range(3)] for u in range(5)]
 assert len(words)>=10
 assert all(counts[u][a]>=(4,3,3)[a] for u in range(5) for a in range(3))
 out.append({'root':r['root'],'supported_words':len(words),'coordinate_support':counts})
(p/'example-verification.json').write_text(json.dumps({'status':'PASS','method':'direct path class counts, no bitset lookup','examples':out,'complete_cover_counts_verified':False},indent=2)+'\n')
print(json.dumps(out))
