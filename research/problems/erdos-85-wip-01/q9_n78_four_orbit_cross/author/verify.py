from pathlib import Path
import json
p=Path(__file__).parent;src=Path('/tmp/erdos85-sol1-q9-n78-four-orbit-order24-parameters');Gs=json.loads((src/'groups.json').read_text());Ps=json.loads((src/'results.json').read_text())['records'];Rs=json.loads((p/'results.json').read_text())['records'];out=[];pairs=0
for r in Rs:
 M=Gs[r['group']]['multiplication'];action=Ps[r['group']]['actions'][r['action']];labels=action['labels']
 for k,s in enumerate(r.get('survivors',[])):
  N=[set() for _ in range(54)]
  def edge(a,b):N[a].add(b);N[b].add(a)
  for f,m in enumerate(action['matching']):edge(f,m)
  for g in range(24):
   edge(labels[g],6+g);edge(labels[g],30+g)
   for u in s['U']:edge(6+g,6+M[g][u])
   for v in s['V']:edge(30+g,30+M[g][v])
   for t in s['T']:edge(6+g,30+M[g][t])
  assert [len(n) for n in N]==[9]*6+[6]*48
  assert all(i not in N[i] and all(i in N[j] for j in N[i]) for i in range(54))
  for i in range(54):
   for j in range(i):assert len(N[i]&N[j])<=1;pairs+=1
  out.append({'root':r['index'],'configuration':k,'group':r['group'],'action':r['action'],'a':r['a'],'neighbors':[sorted(n) for n in N]})
(p/'witnesses.json').write_text(json.dumps(out,indent=2)+'\n');(p/'verification.json').write_text(json.dumps({'graphs':len(out),'codegree_pairs':pairs},indent=2)+'\n');print(len(out),pairs)
