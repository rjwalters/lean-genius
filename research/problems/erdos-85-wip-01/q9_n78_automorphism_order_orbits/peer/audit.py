from pathlib import Path
import hashlib,json,sqlite3,itertools
p=Path(__file__).parent;src=Path('/Users/rwalters/lean-genius-q9-known-values-20260911/n78-automorphism-order-orbits')
pins=json.loads((src/'pins.json').read_text())
for f,h in pins.items():assert hashlib.sha256((src/f).read_bytes()).hexdigest()==h
prem=json.loads((src/'premises.json').read_text());db=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True)
for r in prem:
 assert hashlib.sha256(Path(r['source']).read_bytes()).hexdigest()==r['sha256']
 status,res=db.execute('select status,resolution from review_requests where id=?',(r['review'],)).fetchone();assert status=='resolved' and res.startswith('PASS')
div=[d for d in range(1,49) if 48%d==0]
assert not [t for n in (1,2) for t in itertools.combinations_with_replacement(div,n) if sum(t)==78]
triples=[t for t in itertools.combinations_with_replacement(div,3) if sum(t)==78];assert triples==[(6,24,48)]
patterns=[(c,d,e) for c in range(7) for d in range(7) for e in range(6) if e+8*c+4*d==9];assert set(patterns)=={(1,0,1),(0,1,5),(0,2,1)}
Q=[[1,8,0],[1,5,3],[0,6,3]];sizes=[6,48,24]
assert all(sum(row)==9 for row in Q)
assert all(sizes[i]*Q[i][j]==sizes[j]*Q[j][i] for i in range(3) for j in range(3))
(p/'results.json').write_text(json.dumps({'source_pins':pins,'premises':prem,'divisors':div,'three_orbit_sizes':triples,'degree_patterns':patterns,'quotient':Q},indent=2)+'\n')
print('PASS: source/premise pins, unique orbit triple, three degree patterns and quotient counts')
