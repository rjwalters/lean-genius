import itertools,json,pathlib
# Independent labelled projection: h0,F; f0..f4; a0,b0; x,y,z.
names=['h0','F','f0','f1','f2','f3','f4','a0','b0','x','y','z'];idx={x:i for i,x in enumerate(names)}
rows=[]
for mate in ['x','y','z']:
 other=[x for x in ['x','y','z'] if x!=mate]
 for targets in itertools.permutations(['a0','b0','x','y','z']):
  if targets[0]!=mate or targets[2]!='b0' or targets[4]!='a0':continue
  edges=[('h0',x) for x in ['f0','a0','b0','x','y','z']]+[('F','f'+str(i)) for i in range(5)]+[('f1','f3'),('f0',mate),tuple(other)]+[('f'+str(i),targets[i]) for i in range(5)]
  g=[set() for _ in names]
  for a,b in edges:g[idx[a]].add(idx[b]);g[idx[b]].add(idx[a])
  bad=[(names[a],names[b],[names[x] for x in sorted(g[a]&g[b])]) for a,b in itertools.combinations(range(len(g)),2) if len(g[a]&g[b])>=2]
  assert bad
  cycle=['f1',targets[1],targets[3],'f3']
  assert len(set(cycle))==4 and all(idx[cycle[(i+1)%4]] in g[idx[cycle[i]]] for i in range(4))
  rows.append({'mate':mate,'targets':targets,'forced_cycle':cycle,'violations':bad})
assert len(rows)==6
p=pathlib.Path(__file__).parent
(p/'results.json').write_text(json.dumps({'labelled_assignments':6,'C4_free_survivors':0,'results':rows,'scope':'No-sharing af4/bf2 universal projection; no completion search'},indent=2)+'\n')
print('PASS: all six labelled assignments contain the forced C4')
