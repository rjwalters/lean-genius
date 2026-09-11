import pathlib,json,gzip,itertools,hashlib,sqlite3,time,collections
P=pathlib.Path(__file__).parent;A=pathlib.Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/h7-a7-cycle-incidences');S=A.parent/'h7-a7-cycle-pairing-cover';read=lambda f:json.loads(f.read_text());pins=read(A/'pins.json')
for f,h in pins.items():assert hashlib.sha256((A/f).read_bytes()).hexdigest()==h
for f,h in read(A/'input-pins.json').items():assert hashlib.sha256(pathlib.Path(f).read_bytes()).hexdigest()==h
c=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True);c.row_factory=sqlite3.Row
prem=read(A/'premises.json')
for old in prem:
 live=dict(c.execute('select * from review_requests where id=?',(old['id'],)).fetchone());live['refs']=json.loads(live['refs']);old.pop('expired',None);assert old==live and live['resolution'].startswith('PASS')
bases=read(S/'results.json')['cases'];covers=read(S/'colour-results.json')['cases'];K=list(itertools.combinations(range(7),2));ki={e:i for i,e in enumerate(K)};seen=[0,0];total=[collections.Counter(),collections.Counter()];start=time.monotonic();states=0
with gzip.open(A/'incidences.jsonl.gz','rt') as stream:
 for line in stream:
  assert time.monotonic()-start<60
  r=json.loads(line);ci=r['R_case'];idx=r['colouring_index'];assert idx==seen[ci];seen[ci]+=1
  cr=covers[ci]['representatives'][idx];blocks=bases[ci]['representatives'][cr['pairing_index']]['blocks'];present=[set() for _ in range(7)]
  for colour,block in enumerate(cr['block_cycle']):
   for e in blocks[block]:
    for high in bases[ci]['Q_edges'][e]:present[high].add(colour)
  options=[]
  for hosts in present:
   unused=sorted(set(range(7))-hosts);assert len(unused)==3;row=[]
   for digit,pair in enumerate(itertools.combinations(unused,2)):
    a,b=pair
    if {(a-1)%7,(a+1)%7}&{(b-1)%7,(b+1)%7}:continue
    row.append((digit,1<<ki[pair]))
   options.append(row)
  # Breadth-first labelled row products, fixed ascending high order.
  frontier=[(0,0)]
  for h,row in enumerate(options):
   nxt=[]
   for used,code in frontier:
    states+=1
    for digit,bit in row:
     if not used&bit:nxt.append((used|bit,code+digit*4**h))
   frontier=nxt
  expected={code for used,code in frontier};assert len(expected)==len(frontier)
  assert expected==set(r['solutions']) and len(expected)==len(r['solutions'])
  total[ci]['colourings']+=1;total[ci]['positive']+=bool(expected);total[ci]['solutions']+=len(expected)
summary=read(A/'summary.json');assert summary['status']=='COMPLETE'
for ci,s in enumerate(summary['cases']):assert seen[ci]==len(covers[ci]['representatives'])==s['total'] and total[ci]['positive']==s['positive_colourings'] and total[ci]['solutions']==s['singleton_incidence_choices']
r=dict(status='PASS',cases=list(map(dict,total)),pins=len(pins),states=states,seconds=time.monotonic()-start);(P/'results.json').write_text(json.dumps(r,indent=2)+'\n');print(r)
