import itertools as it,json,hashlib,sqlite3
from pathlib import Path
out=Path(__file__).parent;p=Path('/Users/rwalters/lean-genius-q9-known-values-20260911/n78-s4-one-four-three-six');read=lambda f:json.loads(f.read_text());n=0
for f,root in ((p/'pins.json',p),(p/'input-pins.json',Path('/'))):
 for name,h in read(f).items():assert hashlib.sha256((root/name).read_bytes()).hexdigest()==h;n+=1
con=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True);con.row_factory=sqlite3.Row;r=dict(con.execute('select * from review_requests where id=2257').fetchone());assert r['status']=='resolved' and r['resolution'].startswith('PASS');(out/'premise-state.json').write_text(json.dumps(r,indent=2)+'\n')
P=list(it.permutations(range(4)));pairs=list(it.combinations(range(4),2));cycles=[(0,)+a for a in it.permutations((1,2,3))]
def cycleact(p,c):
 t=tuple(p[x] for x in c);j=t.index(0);return t[j:]+t[:j]
H=[p for p in P if {p[0],p[1]}=={0,1}]
orbits=[];unseen=set(cycles)
while unseen:
 c=min(unseen);O={cycleact(p,c) for p in H};orbits.append(O);unseen-=O
assert sorted(map(len,orbits))==[2,4]
# Check all four invariant B-to-directed-cycle relations, directly via common-neighbor sets.
def diagonal(e,c):return frozenset(e) in (frozenset((c[0],c[2])),frozenset((c[1],c[3])))
answers=[]
for select in ((),(True,),(False,),(True,False)):
 rows=[{j for j,c in enumerate(cycles) if diagonal(e,c) in select} for e in pairs]
 valid=all(len(a&b)<=1 for a,b in it.combinations(rows,2))
 answers.append({'selected':select,'degree':len(rows[0]),'C4_free':valid})
assert [x['C4_free'] for x in answers]==[True,False,False,False]
# All eight B-to-B orbital unions: only empty/equality/complement survive.
bb=[]
for flags in it.product((0,1),repeat=3):
 rows=[{j for j,f in enumerate(pairs) if flags[{2:0,0:1,1:2}[len(set(e)&set(f))]]} for e in pairs]
 if all(len(a&b)<=1 for a,b in it.combinations(rows,2)):bb.append(flags)
assert set(bb)=={(0,0,0),(1,0,0),(0,1,0)}
(out/'checks.json').write_text(json.dumps({'status':'PASS','verified_hashes':n,'B_C4_relations':answers,'B_B_surviving_unions':bb},indent=2)+'\n');print('PASS explicit B/C4 and B/B orbit relations;',n,'hashes')
