"""Exact relabelling quotient of retained character pairs; no graph search."""
import itertools,json,time,hashlib
from pathlib import Path
P=Path(__file__).resolve().parent;B=P.parent
assert not (P/'launch.json').exists()
inputs=json.loads((B/'n80-m16-order4/inputs.json').read_text())
hs={x['source_index']:x['matrix'] for x in inputs}
raw=[json.loads(x) for x in (B/'n80-m16-order4/retained.jsonl').read_text().splitlines()]
def key(h,c):return tuple(h)+tuple(v for z in c for v in z)
records={key(hs[r['source_index']],r['matrix']):r for r in raw}
assert len(records)==len(raw)==1024
phases=[(0,)+p for p in itertools.product(range(4),repeat=4)]
actions=[]
for p in phases:actions.append(tuple((p[i]-p[j])%4 for i in range(5) for j in range(5)))
def move(k,action):
    h=k[:25];c=k[25:];out_h=[];out_c=[]
    for e,t in enumerate(action):
        out_h.append(h[e] if t%2==0 else -h[e]);a,b=c[2*e:2*e+2]
        out_c.extend(((a,b),(-b,a),(-a,-b),(b,-a))[t])
    return tuple(out_h+out_c)
(P/'launch.json').write_text(json.dumps({'inputs':1024,'actions_per_case':256,'seconds':60,'scope':'character-pair relabelling only'})+'\n')
start=time.monotonic();remaining=set(records);orbits=[];transports=[]
while remaining:
    assert time.monotonic()-start<60
    representative=min(remaining);images={}
    for p,a in zip(phases,actions):
        k=move(representative,a);assert k in records
        images.setdefault(k,p)
    assert set(images)<=remaining
    remaining-=set(images)
    index=len(orbits)
    orbits.append({'id':index,'size':len(images),'H':list(representative[:25]),'C':[list(representative[25+2*j:27+2*j]) for j in range(25)]})
    for k,p in images.items():transports.append({'source_index':records[k]['source_index'],'C':records[k]['matrix'],'orbit':index,'phases_from_representative':p})
assert sum(o['size'] for o in orbits)==1024
(P/'orbits.json').write_text(json.dumps(orbits,indent=2)+'\n')
(P/'transports.json').write_text(json.dumps(transports,separators=(',',':'))+'\n')
result={'status':'COMPLETE','inputs':1024,'orbits':len(orbits),'sizes':[o['size'] for o in orbits],'seconds':time.monotonic()-start,
        'scope':'complete character-pair symmetry cover; no graph/lift/exclusion claim'}
(P/'results.json').write_text(json.dumps(result,indent=2)+'\n');print(result)
