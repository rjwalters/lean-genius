"""Read-only audit of the F2 host-to-residual coverage join; no solver calls."""
import gzip
import hashlib
import json
import time
from collections import Counter
from pathlib import Path

SRC = Path('/Users/rwalters/lean-genius-h7-f2-sol2-20260915')
OUT = Path(__file__).parent

def read(p):
    return json.loads(p.read_text())

def records(paths):
    for p in paths:
        with gzip.open(p, 'rt') as f:
            for line in f:
                yield json.loads(line)

def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def run():
    start = time.monotonic()
    launch = read(SRC/'residual/launch.json')
    result = read(SRC/'residual/results.json')
    host = read(SRC/'hosts/results.json')
    high = read(SRC/'high-results.json')
    inputs = [SRC/'host-pins.json', SRC/'residual/launch.json',
              SRC/'residual/results.json', SRC/'residual/source-leaves.jsonl.gz']
    inputs += [SRC/'residual'/n for n in result['receipt_shards']]
    pins = {str(p): digest(p) for p in inputs}
    with (OUT/'join-launch.json').open('x') as f:
        json.dump({'seconds_cap':60, 'pins':pins}, f, indent=2)
    for p,h in read(SRC/'host-pins.json').items():
        assert digest(SRC/p) == h
    assert launch['host_pins_sha256'] == digest(SRC/'host-pins.json')
    assert launch['source_export_sha256'] == digest(SRC/'residual/source-leaves.jsonl.gz')
    expected_keys = [(r['case_index'], p) for r in high['results']
                     for p in range(len(r['pairings']))]
    export = records([SRC/'residual/source-leaves.jsonl.gz'])
    residual = iter(records([SRC/'residual'/n for n in result['receipt_shards']]))
    current = next(residual, None)
    counts = Counter()
    keys = []
    leaves = visited = groups = 0
    retained = []
    frontier = []
    stopped = False
    for h in records([SRC/'hosts'/n for n in host['receipt_shards']]):
        assert time.monotonic()-start < 60
        ci,pi = h['case_index'], h['pairing_index']
        keys.append((ci,pi))
        assert h['receipt']['status'] == 'COMPLETE'
        solutions = h['receipt']['solutions']
        if not solutions:
            continue
        e = next(export)
        assert (e['case_index'],e['pairing_index']) == (ci,pi)
        assert e['hosts'] == [[m >> 21 for m in row] for row in solutions]
        assert all(len(row)==7 and all(m >= 0 and m < 1<<42 and m % (1<<21)==0
                                      for m in row) for row in solutions)
        leaves += len(solutions)
        if current is None:
            stopped = True
            frontier.extend([ci,pi,li] for li in range(len(solutions)))
            continue
        assert not stopped
        assert (current['case_index'],current['pairing_index']) == (ci,pi)
        rr = current['receipts']
        assert len(rr) <= len(solutions)
        for li,r in enumerate(rr):
            status=r['status']
            assert status in ('INFEASIBLE_ROW','INFEASIBLE_ARC','ARC_FEASIBLE','UNKNOWN')
            counts[status]+=1
            visited+=1
            if status in ('ARC_FEASIBLE','UNKNOWN'):
                retained.append([ci,pi,li,status])
        if len(rr)<len(solutions):
            stopped=True
            frontier.extend([ci,pi,li] for li in range(len(rr),len(solutions)))
        groups+=1
        current=next(residual,None)
        assert not stopped or current is None
    assert next(export,None) is None and current is None
    assert keys==expected_keys and len(keys)==24136
    assert leaves==785408==result['total']
    assert visited==result['visited'] and dict(counts)==result['counts']
    assert retained==result['retained'] and len(frontier)==result['unvisited']
    for p,h in pins.items():
        assert digest(Path(p))==h
    summary={'status':'PASS_COVERAGE_JOIN', 'host_inputs':len(keys), 'source_leaves':leaves,
             'visited':visited, 'unvisited':len(frontier), 'counts':dict(counts),
             'negative_only_complete':not frontier and not retained,
             'seconds':time.monotonic()-start,
             'scope':'Exact host export and residual prefix accounting; negative soundness requires endpoint review.'}
    (OUT/'join-result.json').write_text(json.dumps(summary,indent=2)+'\n')
    (OUT/'unvisited.json').write_text(json.dumps(frontier)+'\n')
    print(json.dumps(summary))

if __name__=='__main__':
    run()
