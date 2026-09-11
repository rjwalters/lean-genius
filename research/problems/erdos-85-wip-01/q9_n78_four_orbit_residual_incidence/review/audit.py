from pathlib import Path
import json,hashlib,time,itertools
start=time.monotonic();src=Path('/tmp/erdos85-sol1-q9-n78-four-orbit-residual-incidence');out=Path(__file__).resolve().parent;pins={}
for mf in ['pins.json','input-pins.json']:
 for n,h in json.loads((src/mf).read_text()).items():
  p=src/n;assert hashlib.sha256(p.read_bytes()).hexdigest()==h;pins[str(p)]=h
base=Path('/tmp/erdos85-sol1-q9-n78-four-orbit-order24-parameters');gs=json.loads((base/'groups.json').read_text());actions=json.loads((base/'results.json').read_text())['records'];ws=json.loads(Path('/tmp/erdos85-sol1-q9-n78-four-orbit-cross/witnesses.json').read_text());saved=json.loads((src/'results.json').read_text());assert len(ws)==len(saved['records'])==1344 and saved['status']=='COMPLETE'
assert {w['group'] for w in ws}=={22}
P=list(itertools.permutations(range(4)));ix={p:i for i,p in enumerate(P)};M=[[ix[tuple(p[q[i]] for i in range(4))] for q in P] for p in P];inv=[next(j for j in range(24) if M[j][i]==0) for i in range(24)]
assert M==gs[22]['multiplication'] and inv==gs[22]['inverse']
records=[];codegrees=0
for wi,w in enumerate(ws):
 if time.monotonic()-start>=30:raise TimeoutError('Original independent30s audit cap')
 action=actions[22]['actions'][w['action']];labels=action['labels'];match=action['matching'];original=w['neighbors'];adj=[set() for _ in range(54)]
 def edge(a,b):assert a!=b;adj[a].add(b);adj[b].add(a)
 SU=[v-6 for v in original[6] if 6<=v<30];SV=[v-30 for v in original[30] if v>=30];T=[v-30 for v in original[6] if v>=30]
 assert len(SU)==len(SV)==w['a'] and len(T)==5-w['a']
 for f in range(6):edge(f,match[f])
 for g in range(24):
  edge(6+g,labels[g]);edge(30+g,labels[g])
  for s in SU:edge(6+g,6+M[g][s])
  for s in SV:edge(30+g,30+M[g][s])
  for t in T:edge(6+g,30+M[g][t])
 assert [sorted(a) for a in adj]==original
 assert [len(a) for a in adj]==[9]*6+[6]*48
 masks=[sum(1<<v for v in a) for a in adj]
 for a in range(54):
  for b in range(a):assert (masks[a]&masks[b]).bit_count()<=1;codegrees+=1
 domains=[[v for v in range(48) if labels[v%24]==f and not(masks[6]&masks[6+v])] for f in range(1,6)]
 count=[0];accepted=[]
 def visit(f,chosen,u_count,diffs):
  count[0]+=1
  if u_count>3 or u_count+(6-f)<3:return
  if f==6:accepted.append(chosen);return
  for v in domains[f-1]:
   if any(masks[6+v]&masks[6+x] for x in chosen):continue
   new=set();bad=False
   for x in chosen:
    if v//24!=x//24:continue
    for g in (M[v%24][inv[x%24]],M[x%24][inv[v%24]]):
     if g in diffs or g in new:bad=True;break
     new.add(g)
    if bad:break
   if not bad:visit(f+1,chosen+[v],u_count+int(v<24),diffs|new)
 visit(1,[0],1,set())
 assert not accepted
 r=saved['records'][wi];assert r['index']==wi and r['source_root']==w['root'] and r['source_configuration']==w['configuration'] and r['status']=='INFEASIBLE'
 records.append({'index':wi,'source_root':w['root'],'source_configuration':w['configuration'],'nodes':count[0],'survivors':0})
result={'status':'COMPLETE','original_audit_cap_seconds':30,'seconds':time.monotonic()-start,'graphs':len(ws),'group_products':576,'codegrees':codegrees,'nodes':sum(r['nodes'] for r in records),'survivors':0,'records':records}
assert result['seconds']<30
(out/'input-pins.json').write_text(json.dumps(pins,indent=2)+'\n');(out/'verification.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='records'}))
