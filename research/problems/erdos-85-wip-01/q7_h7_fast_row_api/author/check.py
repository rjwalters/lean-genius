import pathlib,json,importlib.util,time,hashlib
P=pathlib.Path(__file__).parent
mods=[]
for name in ['original','filter']:
 s=importlib.util.spec_from_file_location(name,P/(name+'.py'));m=importlib.util.module_from_spec(s);s.loader.exec_module(m);mods.append(m)
source=P.parent/'h7-row-compatibility/domains.json';out=[]
for seed in json.loads(source.read_text())['results']:
 times=[];answers=[]
 for m in mods:
  t=time.monotonic();answers.append(m.check(seed['adjacency'],max_nodes=100000,deadline=t+60));times.append(time.monotonic()-t)
 assert answers[0]==answers[1]
 # Check the structural equivalence for EVERY guest pair in the input.
 g=list(map(set,seed['adjacency']));H=g[0];V=set(range(7,49))-H
 for u in V:
  for v in V:
   assert bool(g[u]&g[v])==(bool(g[u]&g[v]&set(range(7))) or bool(g[u]&g[v]&H))
 out.append(dict(twins_adjacent=seed['twins_adjacent'],identical_entire_result=True,nodes=answers[0]['nodes'],seconds=times))
(P/'results.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
