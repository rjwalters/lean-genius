import hashlib, itertools, json, pathlib, time
start = time.monotonic()
src = pathlib.Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/residual-eight-2233')
out = pathlib.Path(__file__).parent
for name, digest in json.loads((src/'pins.json').read_text()).items():
    assert hashlib.sha256((src/name).read_bytes()).hexdigest() == digest
saved = json.loads((src/'results.json').read_text())
def normalize(edges):
    return tuple(sorted(tuple(sorted(e)) for e in edges))
edge_orbits = sorted({normalize({(a,b),tuple(sorted((a^1,b^1)))}) for a,b in itertools.combinations(range(8),2)})
assert len(edge_orbits)==16
found=set()
tested=0
for bits in itertools.product((0,1),repeat=16):
    if time.monotonic()-start>30:
        (out/'audit.json').write_text(json.dumps({'status':'UNKNOWN','tested':tested}))
        raise SystemExit('original cap reached')
    tested+=1
    edges=normalize(e for take,orb in zip(bits,edge_orbits) if take for e in orb)
    adj=[set() for _ in range(8)]
    for a,b in edges: adj[a].add(b);adj[b].add(a)
    if [len(a) for a in adj]!=[2,2,2,2,3,3,3,3]:continue
    if any(len(adj[a]&adj[b])>1 for a,b in itertools.combinations(range(8),2)):continue
    found.add(edges)
assert found=={normalize(r['edges']) for r in saved['records']}
maps=[]
for p in itertools.permutations(range(4)):
    if any((i<2)!=(p[i]<2) for i in range(4)):continue
    for flips in itertools.product((0,1),repeat=4):
        maps.append([2*p[i//2]+((i%2)^flips[i//2]) for i in range(8)])
assert len(maps)==64
covered=set();counts=[]
for c in saved['classes']:
    rep=normalize(c['representative_edges'])
    orbit={normalize((m[a],m[b]) for a,b in rep) for m in maps}
    assert len(orbit)==c['count'] and orbit<=found and not orbit&covered
    covered |= orbit;counts.append(len(orbit))
assert covered==found
result={'status':'COMPLETE','original_cap_seconds':30,'seconds':time.monotonic()-start,'binary_edge_orbit_subsets':tested,'C4_free_degree_graphs':len(found),'representative_orbit_sizes':counts,'all_source_pins_verified':True}
(out/'audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
