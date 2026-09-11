from pathlib import Path
import json,hashlib,itertools,time
s=Path('/Users/rwalters/lean-genius-q9-known-values-20260911/n80-m16-character-gauge');o=s.parent/'n80-m16-order4';p=Path(__file__).parent;start=time.monotonic()
for src in [s,o]:
 for f,h in json.loads((src/'pins.json').read_text()).items():assert hashlib.sha256((src/f).read_bytes()).hexdigest()==h
hs={r['source_index']:r['matrix'] for r in json.loads((o/'inputs.json').read_text())}
def key(h,c):return tuple(h)+tuple(tuple(v) for v in c)
raw={key(hs[r['source_index']],r['matrix']) for r in map(json.loads,(o/'retained.jsonl').read_text().splitlines())};assert len(raw)==1024
reps=json.loads((s/'orbits.json').read_text());witnesses=json.loads((s/'transports.json').read_text());seen=set();counts=[0]*4
units=[(1,0),(0,1),(-1,0),(0,-1)]
def mul(a,b):return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def move(rep,t):
 h=[];c=[]
 for i in range(5):
  for j in range(5):
   v=rep['C'][5*i+j];left=units[t[i]];right=units[(-t[j])%4]
   c.append(mul(mul(left,v),right));h.append(rep['H'][5*i+j]*((-1)**(t[i]+t[j])))
 return key(h,c)
for w in witnesses:
 t=w['phases_from_representative'];assert len(t)==5 and t[0]==0 and all(x in range(4) for x in t)
 expected=key(hs[w['source_index']],w['C']);assert expected in raw and expected not in seen
 assert move(reps[w['orbit']],t)==expected;seen.add(expected);counts[w['orbit']]+=1
assert seen==raw and counts==[256]*4
for rep in reps:
 images={move(rep,(0,)+t) for t in itertools.product(range(4),repeat=4)}
 assert len(images)==256 and images<=raw
result=dict(status='PASS_RETAINED_SET_COVER',inputs=1024,witnesses=len(witnesses),orbits=4,sizes=counts,seconds=time.monotonic()-start)
(p/'results.json').write_text(json.dumps(result,indent=2)+'\n');(p/'source-pins.json').write_text((s/'pins.json').read_text());print(result)
