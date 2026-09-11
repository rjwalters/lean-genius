import pathlib,json,itertools,time
P=pathlib.Path(__file__).parent;source=json.loads((P/'results.json').read_text());start=time.monotonic();deadline=start+60;out=[]
for index,r in enumerate(source['representatives']):
 if time.monotonic()>deadline:break
 g=[set() for _ in range(21)]
 def edge(u,v):g[u].add(v);g[v].add(u)
 for x,y in source['F_edges']:edge(x,y)
 for i,h in enumerate(r['singleton_hosts'],7):
  for x in h:edge(i,x)
 rows={};ops=0;status='COMPLETE'
 try:
  for v in range(7,21):
   target=5-2*len(g[v]);domain=[]
   for choice in itertools.combinations([w for w in range(7,21) if w!=v],target):
    ops+=1
    if ops>100000 or time.monotonic()>deadline:raise TimeoutError
    # C4 containing the center: two final neighbors share another neighbor.
    neighbors=list(g[v])+list(choice)
    if any((g[a]&g[b])-{v} for a,b in itertools.combinations(neighbors,2)):continue
    # C4 not containing center impossible: every added edge touches center.
    domain.append(list(choice))
   rows[v]=domain
 except TimeoutError:status='UNKNOWN'
 negative=status=='COMPLETE' and any(not d for d in rows.values())
 out.append(dict(index=index,status=status,operations=ops,negative=negative,rows=rows))
summary=dict(cases=len(out),unvisited=len(source['representatives'])-len(out),negative=sum(r['negative'] for r in out),unknown=sum(r['status']=='UNKNOWN' for r in out),rows=sum(len(d) for r in out for d in r['rows'].values()),seconds=time.monotonic()-start)
(P/'row-results.json').write_text(json.dumps(dict(summary=summary,results=out),separators=(',',':'))+'\n');print(summary)
