"""Local 26-vertex lemma check; no full78-vertex lift or solver."""
from pathlib import Path
import hashlib,itertools,json,time
P=Path(__file__).resolve().parent;S=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/q9-n78-m13-typeb-exclusion')
pins=json.loads((S/'pins.json').read_text())
assert all(hashlib.sha256((S/f).read_bytes()).hexdigest()==h for f,h in pins.items())
start=time.monotonic();witnesses=[]
for t in range(1,7):
    for offsets in itertools.combinations(range(13),3):
        adj=[0]*26
        def edge(a,b):adj[a]|=1<<b;adj[b]|=1<<a
        for a in range(13):
            edge(a,(a+1)%13);edge(13+a,13+(a+t)%13)
            for b in offsets:edge(a,13+(a+b)%13)
        witness=None
        for a,b in itertools.combinations(range(26),2):
            common=adj[a]&adj[b]
            if common.bit_count()>=2:
                x=(common&-common).bit_length()-1;common&=common-1;y=(common&-common).bit_length()-1
                witness=[a,x,b,y];break
        assert witness is not None and len(set(witness))==4
        assert all(adj[witness[i]]>>(witness[(i+1)%4])&1 for i in range(4))
        witnesses.append({'t':t,'offsets':offsets,'cycle':witness})
        assert time.monotonic()-start<60
assert len(witnesses)==1716
(P/'witnesses.json').write_text(json.dumps(witnesses,separators=(',',':'))+'\n')
(P/'input-pins.json').write_text(json.dumps(pins,indent=2)+'\n')
result={'status':'PASS','local_cases':1716,'explicit_C4_witnesses':len(witnesses),'seconds':time.monotonic()-start,
        'scope':'complete local two-orbit test supporting paper lemma; no full78graph/SAT search'}
(P/'results.json').write_text(json.dumps(result,indent=2)+'\n');print(result)
