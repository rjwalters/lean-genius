import pathlib,json,gzip,time,sqlite3,hashlib,importlib.util,itertools,collections
P=pathlib.Path(__file__).parent;A=pathlib.Path('/tmp/erdos85-sol1-h7-projection-extension');B=P.parent/'h7-singleton-host-row-shortcut'
def module(name,path):
 spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
assert not (P/'launch.json').exists() and not (P/'results.json').exists(),'No overwrite or retry'
c=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True);c.row_factory=sqlite3.Row;premises=[]
for rid in [2110,2113]:
 r=dict(c.execute('select * from review_requests where id=?',(rid,)).fetchone());assert r['status']=='resolved' and r['resolution'].startswith('PASS');premises.append(r)
for root in [A,B]:
 for f,h in json.loads((root/'pins.json').read_text()).items():assert hashlib.sha256((root/f).read_bytes()).hexdigest()==h
with gzip.open(A/'results.json.gz','rt') as f:data=json.load(f)
assert data['summary']['unvisited']==0 and all(r['status']=='COMPLETE' for r in data['results'])
source=json.loads((A/'source-results.json').read_text());completion=json.loads((A/'source-completion-results.json').read_text());edges={(r['source_index'],j):es for r in completion['results'] for j,es in enumerate(r['solutions'])};ext=module('extension',A/'run.py');api=module('shortcut',B/'compact.py')
(P/'premises.json').write_text(json.dumps(premises,indent=2)+'\n');(P/'launch.json').write_text(json.dumps(dict(cases=len(data['results']),assignments=sum(len(r['solutions']) for r in data['results']),limit_seconds=60,operations_per_assignment=126))+'\n')
start=time.monotonic();deadline=start+60;out=[];survivors=[];tested=0
for ci,r in enumerate(data['results']):
 codes=[];plans={};base=None
 if time.monotonic()<deadline:base=ext.base(source['representatives'][r['source_index']],edges[r['source_index'],r['singleton_index']],source['F_edges'])
 for ai,(pairing,matchings) in enumerate(r['solutions']):
  if time.monotonic()>deadline:break
  key=tuple(pairing)
  if key not in plans:
   adj=ext.full_graph(base,pairing,matchings);plan=api.prepare(adj);assert len(plan)==14 and sum(len(cs) for s,b,cs in plan)==126<100000;plans[key]=plan
  hosts={v:0 for v in range(21,42)}
  for e,mask in enumerate(matchings):
   while mask:
    bit=mask&-mask;j=bit.bit_length()-1;assert not hosts[21+j];hosts[21+j]=1<<(42+e);mask-=bit
  rows=api.evaluate(plans[key],hosts);bad=next((s for s,rs in rows.items() if not rs),None)
  if bad is None:codes.append('.');survivors.append([ci,ai])
  else:assert 7<=bad<=20;codes.append(chr(65+bad-7))
  tested+=1
 out.append(dict(case_index=ci,source_index=r['source_index'],singleton_index=r['singleton_index'],total=len(r['solutions']),visited=len(codes),unvisited=len(r['solutions'])-len(codes),negative=len(codes)-codes.count('.'),survivors=codes.count('.'),certificates=''.join(codes)))
summary=dict(status='COMPLETE' if all(r['unvisited']==0 for r in out) else 'UNKNOWN',cases=len(out),assignments=sum(r['total'] for r in out),visited=tested,unvisited=sum(r['unvisited'] for r in out),negative=sum(r['negative'] for r in out),survivors=len(survivors),candidate_tests=tested*126,seconds=time.monotonic()-start)
(P/'results.json').write_text(json.dumps(dict(summary=summary,results=out),separators=(',',':'))+'\n');(P/'survivors.json').write_text(json.dumps(survivors,separators=(',',':'))+'\n');print(summary)
