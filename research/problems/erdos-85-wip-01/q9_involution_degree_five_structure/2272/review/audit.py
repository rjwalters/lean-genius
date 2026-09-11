from pathlib import Path
import json,hashlib,itertools,sqlite3
p=Path(__file__).parent;src=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/q9-involution-n80-degree-five-centers')
pins=json.loads((src/'pins.json').read_text())
for f,h in pins.items():assert hashlib.sha256((src/f).read_bytes()).hexdigest()==h
for f,h in json.loads((src/'input-pins.json').read_text()).items():assert hashlib.sha256(Path(f).read_bytes()).hexdigest()==h
db=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True)
for record in json.loads((src/'accepted-premises.json').read_text()):
 s,r=db.execute('select status,resolution from review_requests where id=?',(record['id'],)).fetchone();assert s=='resolved' and r.startswith('PASS')
retained=[];counts=[]
for gi,rep in enumerate(json.loads((src/'representatives.json').read_text())):
 G=[set() for _ in range(10)]
 for a,b in rep['edges']:G[a].add(b);G[b].add(a)
 assert all(len(x)==3 for x in G) and all(len(G[i]&G[j])<=1 for i,j in itertools.combinations(range(10),2))
 local=[0,0]
 for Ptuple in itertools.combinations(range(10),4):
  P=set(Ptuple);M=set(range(10))-P;d=[len(n&P) for n in G]
  if min(d)<1 or any(d[i]>2 for i in M):continue
  dp=sorted(d[i] for i in P);dm=sorted(len(G[i]&M) for i in M)
  if dp==[1,1,1,3]:kind='star';assert dm==[2]*6;local[0]+=1
  else:
   assert dp==[1]*4 and dm==[1,1,2,2,2,2];kind='matching_path';local[1]+=1
   seen={next(iter(M))}
   while True:
    grown=seen|set().union(*(G[i]&M for i in seen))
    if grown==seen:break
    seen=grown
   assert seen==M
  retained.append({'graph_index':gi,'P':list(Ptuple),'kind':kind,'degree_P':d})
 counts.append(local)
assert retained==json.loads((src/'results.json').read_text())['retained']
assert counts==[[10,0],[4,0],[1,9]]
(p/'results.json').write_text(json.dumps({'source_pins':pins,'marked_cases_checked':630,'retained':24,'counts_by_graph_star_matching':counts,'correction_totals':[4,2,0]},indent=2)+'\n')
print('PASS630 markedcases:15stars+9matching/path; allpins andpremises verified')
