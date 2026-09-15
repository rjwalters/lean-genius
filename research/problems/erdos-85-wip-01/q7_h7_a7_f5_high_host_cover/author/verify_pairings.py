"""Independent full permutation enumeration for completed a7 slices."""
import hashlib
import itertools
import json
from pathlib import Path
import sys
import time

target = Path(sys.argv[1])
findex = int(sys.argv[2])
dest = Path(sys.argv[3])
launch = json.loads((target/'high-launch.json').read_text())
root = Path(launch['source_path'])
for name, digest in launch['source_pins'].items():
    assert hashlib.sha256((root/name).read_bytes()).hexdigest() == digest
assert hashlib.sha256((target/'highs.py').read_bytes()).hexdigest() == launch['source_script_sha256']
cover = json.loads((root/'results.json').read_text())
done = json.loads((root/'completion-results.json').read_text())
records = [r for r in done['results'] if r['F_index'] == findex]
expected = {i for i,r in enumerate(cover['representatives']) if r['F_index'] == findex}
assert len(records) == len(expected) == 28
assert {r['source_index'] for r in records} == expected
assert all(r['status'] == 'COMPLETE' for r in records)
cases = [(r['source_index'],j,e) for r in records for j,e in enumerate(r['solutions'])]
result = json.loads((target/'high-results.json').read_text())
assert len(cases) == len(result['results'])
perms = list(itertools.permutations(range(7)))
total = positive = 0
start = time.monotonic()
for n, ((si,sj,edges),row) in enumerate(zip(cases,result['results'])):
    assert row['status'] == 'COMPLETE'
    assert (row['case_index'],row['source_index'],row['singleton_index']) == (n,si,sj)
    rep = cover['representatives'][si]
    adj = [[False]*21 for _ in range(21)]
    for u,v in rep['F_edges']+edges:
        assert u != v
        adj[u][v] = adj[v][u] = True
    for s,hosts in enumerate(rep['singleton_hosts'],7):
        for e in hosts:
            adj[s][e] = adj[e][s] = True
    ok = [[not adj[14+h][7+d] and
           sum(adj[14+h][v] and adj[7+d][v] for v in range(21)) == 0
           for d in range(7)] for h in range(7)]
    actual = {p for p in perms if all(ok[h][p[h]] for h in range(7))}
    saved = [tuple(p) for p in row['pairings']]
    assert len(saved) == len(set(saved)) and set(saved) == actual
    total += len(actual)
    positive += bool(actual)
assert result['summary']['pairings'] == total
assert result['summary']['positive'] == positive
receipt = {'status':'PASS', 'F_index':findex, 'source_cases':len(cases),
           'positive':positive,'negative':len(cases)-positive,'pairings':total,
           'method':'all 5040 permutations, Boolean adjacency and explicit common-neighbor counting',
           'source_pins':launch['source_pins'],
           'high_results_sha256':hashlib.sha256((target/'high-results.json').read_bytes()).hexdigest(),
           'seconds':time.monotonic()-start,
           'scope':'Complete high-pairing cover only; pair hosts and residual edges remain open.'}
dest.parent.mkdir(parents=True,exist_ok=True)
dest.write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
