from pathlib import Path
import json,hashlib,itertools,math
s=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/control63-m21-fourier-obstruction');p=Path(__file__).parent
pins=json.loads((s/'pins.json').read_text())
for f,h in pins.items():assert hashlib.sha256((s/f).read_bytes()).hexdigest()==h
cert=json.loads((s/'results.json').read_text());records={tuple(r['shifts']):r['obstruction'] for r in cert['records']};assert len(records)==120
ordered=duplicates=0
for shifts in itertools.product(range(1,11),repeat=3):
 ordered+=1
 if len(set(shifts))<3:duplicates+=1;continue
 key=tuple(sorted(shifts));o=records[key];k=o['k'];assert math.gcd(k,21)==1
 # Use signed representatives in [-10,10], then the exact cosine-sum sign rule.
 residues=[((k*a+10)%21)-10 for a in key]
 folded=list(map(abs,residues));sums=[folded[i]+folded[j] for i,j in [(0,1),(0,2),(1,2)]]
 assert min(sums)<=10<max(sums)
 assert folded==o['folded'] and sums==o['pair_sums']
 assert o['signs']==[1 if 2*t<21 else -1 for t in sums]
assert ordered==1000 and duplicates==280
(p/'source-pins.json').write_text(json.dumps(pins,indent=2)+'\n')
(p/'results.json').write_text(json.dumps(dict(status='PASS',ordered_triples=ordered,common_shift_excluded=duplicates,distinct_ordered=ordered-duplicates,certificate_entries=len(records)),indent=2)+'\n')
print('PASS:1000 ordered triples,280 common-shift exclusions,720 distinct ordered cases certified')
