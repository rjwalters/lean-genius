"""Independent graph/orbit oracle and frozen control regeneration; no solver."""
import hashlib, importlib.util, itertools, json, time
from pathlib import Path

ROOT=Path(__file__).resolve().parent
SOURCE=Path('/tmp/erdos85-sol1-q9-semiregular')
CONTROL=Path('/tmp/erdos85-sol1-q9-control48')
pins=json.loads((SOURCE/'payload-pins.json').read_text())
assert all(hashlib.sha256((SOURCE/f).read_bytes()).hexdigest()==h for f,h in pins.items())
spec=importlib.util.spec_from_file_location('producer',SOURCE/'generate.py')
producer=importlib.util.module_from_spec(spec);spec.loader.exec_module(producer)

def orbit_partition(n,m):
    pairs=set(itertools.combinations(range(n),2)); result=set()
    def move(v): return m*(v//m)+(v%m+1)%m
    while pairs:
        first=min(pairs); orbit=set(); pair=first
        while pair not in orbit:
            orbit.add(pair);pair=tuple(sorted(map(move,pair)))
        assert pair==first and orbit<=pairs
        pairs-=orbit;result.add(frozenset(orbit))
    return result

start=time.monotonic(); tested=0; cases=[]
for n,m in [(3,1),(4,1),(4,2),(4,4),(5,1),(5,5),(6,2),(6,3),(6,6),(8,4)]:
    partition=orbit_partition(n,m)
    for d in range(n):
        c,meta=producer.build(n,m,d)
        assert {frozenset(map(tuple,o['edges'])) for o in meta['orbits']}==partition
        variables=[o['var'] for o in meta['orbits']]
        assert len(variables)==len(set(variables))
        for bits in itertools.product((False,True),repeat=len(variables)):
            values={1:True,**dict(zip(variables,bits))}
            # Independent evaluation of the AND circuit, not producer.extension.
            for z,a,b in c.gates:
                assert z not in values and abs(a) in values and abs(b) in values
                values[z]=(values[abs(a)] if a>0 else not values[abs(a)]) and (values[abs(b)] if b>0 else not values[abs(b)])
            assert set(values)==set(range(1,c.nvars+1))
            encoded=all(any(values[abs(x)] if x>0 else not values[abs(x)] for x in clause) for clause in c.clauses)
            edges={tuple(e) for bit,o in zip(bits,meta['orbits']) if bit for e in o['edges']}
            degree=[sum(v in e for e in edges) for v in range(n)]
            c4=False
            # Four-vertex cycle oracle, separate from common-neighbour encoding.
            for a,b,c0,e in itertools.combinations(range(n),4):
                for cycle in ((a,b,c0,e),(a,b,e,c0),(a,c0,b,e)):
                    if all(tuple(sorted((cycle[i],cycle[(i+1)%4]))) in edges for i in range(4)):
                        c4=True;break
                if c4:break
            expected=min(degree)>=d and not c4
            assert encoded==expected,(n,m,d,bits)
            tested+=1
        cases.append([n,m,d,2**len(variables)])

c,meta=producer.build(48,24,7)
actual=json.loads((CONTROL/'map.json').read_text())
assert all(actual[k]==v for k,v in json.loads(json.dumps(meta)).items())
assert actual['generator_sha256']==pins['generate.py']
data=('p cnf %d %d\n'%(c.nvars,len(c.clauses))+''.join(' '.join(map(str,clause))+' 0\n' for clause in c.clauses)).encode()
assert data==(CONTROL/'graph.cnf').read_bytes()
assert hashlib.sha256(data).hexdigest()==actual['cnf_sha256']
assert {frozenset(map(tuple,o['edges'])) for o in meta['orbits']}==orbit_partition(48,24)
result={'status':'PASS','assignments':tested,'cases':cases,'seconds':time.monotonic()-start,
        'control':{'n':48,'m':24,'d':7,'variables':c.nvars,'clauses':len(c.clauses),'cnf_sha256':actual['cnf_sha256']},
        'scope':'independent translation-orbit partition and exhaustive four-cycle/degree oracle; exact frozen control regeneration; no graph solver launch'}
(ROOT/'results.json').write_text(json.dumps(result,indent=2)+'\n')
(ROOT/'input-pins.json').write_text(json.dumps({'generator':pins,'control':{f:hashlib.sha256((CONTROL/f).read_bytes()).hexdigest() for f in ('map.json','graph.cnf')}},indent=2)+'\n')
print(json.dumps(result))
