import hashlib, itertools, json, time
from pathlib import Path
source = Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/q9-n80-m8-local-constraints')
for name, digest in json.loads((source/'pins.json').read_text()).items():
    assert hashlib.sha256((source/name).read_bytes()).hexdigest() == digest
start = time.monotonic()
internal = []
for mask in range(16):
    s = {x for k, pair in enumerate([(1,7),(2,6),(3,5),(4,)]) if mask >> k & 1 for x in pair}
    adj = [sum(1 << ((x+t)%8) for t in s) for x in range(8)]
    if all((adj[x]&adj[y]).bit_count() <= 1 for x in range(8) for y in range(x)):
        internal.append(s)
assert {tuple(sorted(s)) for s in internal} == {(),(4,),(1,7),(3,5)}
counts = {}
tested = survivors = 0
for a,b in itertools.product(internal,repeat=2):
    for mask in range(256):
        T = [t for t in range(8) if mask >> t & 1]
        edges = set()
        for x in range(8):
            for offset,S in [(0,a),(8,b)]:
                for t in S: edges.add(tuple(sorted((offset+x,offset+(x+t)%8))))
            for t in T: edges.add((x,8+(x+t)%8))
        adj = [0]*16
        for x,y in edges: adj[x] |= 1 << y; adj[y] |= 1 << x
        tested += 1
        if any((adj[x]&adj[y]).bit_count()>1 for x in range(16) for y in range(x)): continue
        survivors += 1
        d = len(T)
        assert d <= 3
        diff = [min((x-y)%8,(y-x)%8) for x,y in itertools.combinations(T,2)]
        assert 4 not in diff and len(set(diff)) == len(diff)
        if d == 3: assert set(diff)=={1,2,3} and len(a)<2 and len(b)<2
        if d and a == b: assert not a
        if d == 2 and (len(a)==2 or len(b)==2): assert diff[0] in (1,3)
        order = [set(),{4},{1,7},{3,5}]
        key = (order.index(a),order.index(b),d)
        counts[key] = counts.get(key,0)+1
expected = json.loads((source/'results.json').read_text())
assert counts == {(r['a'],r['b'],r['cross_degree']):r['count'] for r in expected['pair_counts']}
result = dict(status='PASS', internal_sets_checked=16, pair_cases=tested, survivors=survivors,
              exact_peer_counts_match=True, seconds=time.monotonic()-start)
Path(__file__).with_name('results.json').write_text(json.dumps(result,indent=2)+'\n')
print(result)
