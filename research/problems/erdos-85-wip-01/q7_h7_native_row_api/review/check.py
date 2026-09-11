import pathlib,json,gzip,importlib.util,time,hashlib,copy,collections
P=pathlib.Path(__file__).parent
S=pathlib.Path('/tmp/erdos85-sol1-h7-crossed9-arc')
def imp(name,p):
 s=importlib.util.spec_from_file_location(name,p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
native=imp('native',P/'native.py');ref=imp('reference',pathlib.Path('/Users/rwalters/lean-genius-q7-outside-first-20260910/h7-fast-row-api/filter.py'))
pins=json.loads((S/'pins.json').read_text())
for f,h in pins.items():assert hashlib.sha256((S/f).read_bytes()).hexdigest()==h
with gzip.open(S/'results.json.gz','rt') as f:data=json.load(f)['results']
fixtures=[]
for status in ['INFEASIBLE_LOCAL','INFEASIBLE_ARC']:
 candidates=[r for r in data if r['status']==status]
 fixtures.extend(candidates[i] for i in [1,7,len(candidates)//3,len(candidates)//2+1,len(candidates)-2])
records=[];expired=0;invalid=0
for r in fixtures:
 g=r['adjacency'];full=ref.check(g);assert full['status']==r['status']
 caps=sorted({0,1,2,31,255,1000,full['nodes']//2,full['nodes']-1,full['nodes'],100000})
 for cap in caps:
  a=ref.check(g,max_nodes=cap);b=native.check(g,max_nodes=cap);assert a==b,(r['assignment_index'],cap)
  records.append({'assignment_index':r['assignment_index'],'cap':cap,'nodes':a['nodes'],'status':a['status'],'stage':a.get('stage'),'events':len(a['events'])})
 for budget in [0,100000]:
  deadline=time.monotonic()-1
  assert ref.check(g,max_nodes=budget,deadline=deadline)==native.check(g,max_nodes=budget,deadline=deadline);expired+=1
for mutation in ['selfloop','asymmetric','out_of_range','short','high_degree']:
 g=copy.deepcopy(fixtures[0]['adjacency'])
 if mutation=='selfloop':g[0].append(0)
 if mutation=='asymmetric':g[g[0][0]].remove(0)
 if mutation=='out_of_range':g[0].append(49)
 if mutation=='short':g.pop()
 if mutation=='high_degree':
  v=g[0].pop();g[v].remove(0)
 try:native.check(g)
 except ValueError:invalid+=1
 else:raise AssertionError(mutation)
out={'status':'PASS_FIXTURE_EQUIVALENCE','fixtures':len(fixtures),'comparisons':len(records),'expired_deadlines':expired,'invalid_inputs_rejected':invalid,'statuses':dict(collections.Counter(r['status'] for r in records)),'unknown_stages':dict(collections.Counter(r['stage'] for r in records if r['status']=='UNKNOWN')),'clock_delta':abs(native.lib.native_now()-time.monotonic()),'source_sha256':hashlib.sha256((P/'filter.cpp').read_bytes()).hexdigest(),'records':records,'scope':'Independent compilation, different previously terminal crossed9 fixtures only. No new search or capped-case retries.'}
(P/'results.json').write_text(json.dumps(out,indent=2)+'\n');print({k:v for k,v in out.items() if k!='records'})
