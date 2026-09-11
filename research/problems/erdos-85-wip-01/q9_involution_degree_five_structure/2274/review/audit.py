from pathlib import Path
import itertools,json,hashlib,collections
p=Path(__file__).parent;src=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/q9-involution-n80-degree-five-attachments')
pins=json.loads((src/'pins.json').read_text())
for f,h in pins.items():assert hashlib.sha256((src/f).read_bytes()).hexdigest()==h
for f,h in json.loads((src/'input-pins.json').read_text()).items():assert hashlib.sha256(Path(f).read_bytes()).hexdigest()==h
out=[]
for t in range(3):
 G=[set() for _ in range(10)]
 def edge(a,b):G[a].add(b);G[b].add(a)
 edge(0,1)
 for a in (2,4,6,8):edge(0,a);edge(1,a+1)
 for a,b in [(2,4),(6,8)][:t]:edge(a,b);edge(a+1,b+1)
 counts=collections.Counter();central=[]
 for mask in range(1024):
  S={i for i in range(10) if mask>>i&1}
  if S&{i^1 for i in S}:continue
  if any(G[a]&G[b] for a,b in itertools.combinations(S,2)):continue
  counts[len(S)]+=1
  if len(S)==2 and 0 in S:central.append(sorted(S))
 out.append({'t':t,'subsets_checked':1024,'max_size':max(counts),'allowed_central_pairs':central,'subset_counts':{str(k):v for k,v in sorted(counts.items())}})
assert out==json.loads((src/'results.json').read_text())
roots=json.loads((src.parent/'q9-involution-n80-t01-incidence/results.json').read_text())['results'];rows=[]
for i,e in enumerate(roots):
 if e['t']!=0 or e['status']!='WITNESS':continue
 ordinary=[f for f in e['case']['P'] if sum(e['witness'][f])==2]
 rows.append({'root_index':i,'ordinary_centers_in_P':ordinary,'rejected_saved_witness':bool(ordinary)})
assert rows==json.loads((src/'saved-witness-filter.json').read_text())['rows']
assert len(rows)==24 and sum(r['rejected_saved_witness'] for r in rows)==14
(p/'results.json').write_text(json.dumps({'source_pins':pins,'local_subset_checks':3072,'local_results':out,'saved_witnesses_filtered':24,'rejected_certificates_only':14,'roots_excluded':0},indent=2)+'\n')
print('PASS3072 subsets; maximum2; centralpair counts4/2/0;14 savedcertificates rejected, zero roots excluded')
