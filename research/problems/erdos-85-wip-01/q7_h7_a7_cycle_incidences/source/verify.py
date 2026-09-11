from pathlib import Path
import json,gzip,itertools,hashlib,time,collections
P=Path(__file__).parent;S=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/h7-a7-cycle-pairing-cover');start=time.monotonic()
pins=json.loads((P/'input-pins.json').read_text())
for f,h in pins.items():assert hashlib.sha256(Path(f).read_bytes()).hexdigest()==h
bases=json.loads((S/'results.json').read_text())['cases'];covers=json.loads((S/'colour-results.json').read_text())['cases'];pi={e:i for i,e in enumerate(itertools.combinations(range(7),2))};totals=[collections.Counter(),collections.Counter()];seen=[0,0];dpstates=0
with gzip.open(P/'incidences.jsonl.gz','rt') as stream:
 for line in stream:
  if time.monotonic()-start>60:raise TimeoutError
  row=json.loads(line);ci=row['R_case'];idx=row['colouring_index'];assert idx==seen[ci] and ci in [0,1];seen[ci]+=1
  c=covers[ci]['representatives'][idx];b=bases[ci]['representatives'][c['pairing_index']]['blocks'];phi={tuple(bases[ci]['Q_edges'][e]):x for x,k in enumerate(c['block_cycle']) for e in b[k]}
  unused=[sorted(set(range(7))-{x for e,x in phi.items() if h in e}) for h in range(7)];choices=[list(itertools.combinations(U,2)) for U in unused]
  options=[[(j,1<<pi[p]) for j,p in enumerate(cs) if (p[1]-p[0])%7 not in [2,5]] for cs in choices]
  # Reverse-high weighted subset DP, independently of MRV recursive enumeration.
  dp={0:1}
  for h in reversed(range(7)):
   nxt=collections.Counter()
   for used,n in dp.items():
    for j,bit in options[h]:
     if not used&bit:nxt[used|bit]+=n
   dp=nxt;dpstates+=len(dp)
  exact=sum(dp.values());codes=row['solutions'];assert len(set(codes))==len(codes)==exact
  maps=[dict(row) for row in options]
  for code in codes:
   assert 0<=code<16384;used=0
   for h in range(7):
    j=(code>>(2*h))&3;assert j in maps[h];bit=maps[h][j];assert not used&bit;used|=bit
  totals[ci]['colourings']+=1;totals[ci]['positive']+=bool(codes);totals[ci]['solutions']+=len(codes)
summary=json.loads((P/'summary.json').read_text());assert summary['status']=='COMPLETE'
for ci,r in enumerate(summary['cases']):
 assert seen[ci]==len(covers[ci]['representatives'])==r['total']==r['visited']
 assert totals[ci]['positive']==r['positive_colourings'] and totals[ci]['solutions']==r['singleton_incidence_choices']
for f,h in pins.items():assert hashlib.sha256(Path(f).read_bytes()).hexdigest()==h
r={'status':'PASS','cases':list(map(dict,totals)),'dp_states':dpstates,'seconds':time.monotonic()-start,'scope':'All stored codes valid/unique, exact completeness by independent reverse-high weighted subsetDP on all78723fixed propercolourings. No remaininglowedges or fullH7 exclusion.'};(P/'verification.json').write_text(json.dumps(r,indent=2)+'\n');print(r)
