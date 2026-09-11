from pathlib import Path
import json,importlib.util,time,collections,copy,hashlib
P=Path(__file__).parent
def imp(name,p):
 s=importlib.util.spec_from_file_location(name,p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
ref=imp('reference',Path('/tmp/erdos85-sol1-h7-empty-first-row-api/filter.py'));native=imp('native',P/'native.py')
a6=json.loads(Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/review2101/fixtures.json').read_text());a7=json.loads(Path('/tmp/erdos85-sol1-h7-empty-first-row-api/fixtures.json').read_text())
perm=list(range(7))+[7+(v-7+11)%42 for v in range(7,49)]
def relabel(g):
 out=[[] for _ in g]
 for u,ns in enumerate(g):out[perm[u]]=sorted(perm[v] for v in ns)
 return out
fixtures=a6+[relabel(g) for g in a6+a7];assert len(fixtures)==12
records=[];expired=0
for i,g in enumerate(fixtures):
 full=ref.check(g);assert full['status']!='UNKNOWN'
 for cap in sorted({0,1,31,500,1000,full['nodes']//2,full['nodes']-1,full['nodes'],full['nodes']+1,100000}):
  a=ref.check(g,max_nodes=cap);b=native.check(g,max_nodes=cap);assert a==b,(i,cap)
  records.append({'fixture':i,'budget':cap,'nodes':a['nodes'],'status':a['status'],'stage':a.get('stage'),'events':len(a.get('events',[]))})
 deadline=time.monotonic()-1;assert ref.check(g,deadline=deadline)==native.check(g,deadline=deadline);expired+=1
invalid=0
for mode in ['loop','asymmetric','badvertex','short','activeedge','highdegree']:
 g=copy.deepcopy(fixtures[0])
 if mode=='loop':g[0].append(0)
 if mode=='asymmetric':g[g[0][0]].remove(0)
 if mode=='badvertex':g[0].append(49)
 if mode=='short':g.pop()
 if mode=='activeedge':g[7].append(8);g[8].append(7)
 if mode=='highdegree':v=g[0].pop();g[v].remove(0)
 try:native.check(g)
 except ValueError:invalid+=1
 else:raise AssertionError(mode)
clock=abs(native.lib.native_now()-time.monotonic());assert clock<.01
r={'status':'PASS','independent_compilation':True,'fixtures':len(fixtures),'whole_object_equalities':len(records),'expired_deadlines':expired,'invalid_inputs_rejected':invalid,'clock_delta':clock,'records':records,'source_sha256':hashlib.sha256((P/'filter.cpp').read_bytes()).hexdigest(),'scope':'Five different a6fixtures plus seven arbitrary-low relabelled fixtures; exact node-boundary result equality. No family search or oldcappedcase retry.'}
(P/'results.json').write_text(json.dumps(r,indent=2)+'\n');print({k:v for k,v in r.items() if k!='records'})
