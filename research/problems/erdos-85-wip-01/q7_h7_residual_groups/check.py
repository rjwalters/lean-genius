import pathlib,json,hashlib
P=pathlib.Path(__file__).parent;S=P/'host-samples.json';data=json.loads(S.read_text());out=[]
for row in data['results']:
 g=list(map(set,row['sample'][0]));H=sorted(g[0]);outside=set(range(7,49))-set(H);w=lambda u:len(g[u]&set(range(7)))
 groups={h:sorted(g[h]&outside) for h in H};mate={h:next(iter(g[h]&set(H))) for h in H}
 assert len(H)==8 and len(outside)==34 and set().union(*map(set,groups.values()))==outside
 allowed={}
 for h in H:
  assert len(groups[h])==6-w(h)
  for u in groups[h]:
   forbidden={mate[h]}|{k for k in H if (g[u]&g[k]&set(range(1,7)))}
   assert len(forbidden)==1+w(u)
   allowed[u]=set(H)-forbidden;assert len(allowed[u])==7-w(u)
 A=[[sum(k in allowed[u] for u in groups[h]) for k in H] for h in H]
 for i,h in enumerate(H):
  for j,k in enumerate(H):
   assert A[i][j]==(0 if mate[h]==k else 7-w(h)-w(k))==A[j][i]
  demand=sum(6-w(u) for u in groups[h]);assert sum(A[j][i] for j in range(8))-demand==len(groups[h])
 out.append({'twins_adjacent':row['twins_adjacent'],'hosts':H,'sizes':[len(groups[h]) for h in H],'availability':A})
(P/'results.json').write_text(json.dumps({'samples_checked':2,'results':out,'source_sha256':hashlib.sha256(S.read_bytes()).hexdigest(),'scope':'Structural availability identities on sample host assignments only; no completion or exclusion'},indent=2)+'\n');print('PASS both host samples: exact forbidden counts, symmetric availability, column deficit identities')
