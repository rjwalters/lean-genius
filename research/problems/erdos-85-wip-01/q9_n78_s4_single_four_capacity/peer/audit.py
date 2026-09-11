import json,hashlib,sqlite3,itertools as it
from pathlib import Path
out=Path(__file__).parent;p=Path('/Users/rwalters/lean-genius-q9-known-values-20260911/n78-s4-single-four-capacity');read=lambda f:json.loads(f.read_text());n=0
for f,root in ((p/'pins.json',p),(p/'input-pins.json',Path('/'))):
 for name,h in read(f).items():assert hashlib.sha256((root/name).read_bytes()).hexdigest()==h;n+=1
con=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True);con.row_factory=sqlite3.Row;states=[]
for id in (2257,2376):
 r=dict(con.execute('select * from review_requests where id=?',(id,)).fetchone());assert r['status']=='resolved' and r['resolution'].startswith('PASS');states.append(r)
(out/'premise-states.json').write_text(json.dumps(states,indent=2)+'\n')
r=read(Path('/Users/rwalters/lean-genius-q9-known-values-20260911/n78-s4-character/results.json'));P=list(it.permutations(range(4)))
def order(p):
 q=tuple(range(4));k=0
 while True:
  q=tuple(p[x] for x in q);k+=1
  if q==tuple(range(4)):return k
selected=[]
for sizes in ([4,6,8,12,12,12,24],[4,6,6,6,8,12,12,24]):
 sols=[s for s in r['solutions'] if s['sizes']==sizes];assert len(sols)==1
 for j in sols[0]['indices']:
  ch=r['characters'][j];v=ch['values']
  for H in ch['subgroups']:
   if v[0]==6:assert v==[6,0,0,2,2] and sorted(order(P[h]) for h in H)==[1,2,4,4]
   elif v[0]==12:
    assert len(H)==2;h=next(h for h in H if h);fixed=sum(i==P[h][i] for i in range(4))
    assert (v,fixed) in [([12,0,0,4,0],0),([12,2,0,0,0],2)]
 selected.append(sols[0])
# F exterior degrees from balance and pair capacity alone.
choices={}
for size in (8,12,24):
 choices[size]=[a for a in range(10) if 4*a%size==0 and size*((4*a//size)*(4*a//size-1)//2)<=6]
assert choices=={8:[0,2],12:[0,3],24:[0,6]}
assignments=[(v,b,c,u) for v,b,c,u in it.product(choices[8],choices[12],choices[12],choices[24]) if v+b+c+u==9]
assert assignments==[(0,0,3,6),(0,3,0,6)]
(out/'checks.json').write_text(json.dumps({'status':'PASS','verified_hashes':n,'solutions':selected,'F_degree_assignments':assignments},indent=2)+'\n');print('PASS',n,'hashes, full subgroup bridge and degree assignments')
