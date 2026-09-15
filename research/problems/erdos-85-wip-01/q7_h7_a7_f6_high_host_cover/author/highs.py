"""Single bounded high-assignment pass over the complete F6 projection."""
import collections
import hashlib
import itertools
import json
import time
from pathlib import Path

ROOT = Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration/research/problems/erdos-85-wip-01')
SOURCE = ROOT / 'q7_h7_a7_noncycle_singleton_projection/author'
OUT = Path(__file__).parent

def inputs():
    cover = json.loads((SOURCE / 'results.json').read_text())
    done = json.loads((SOURCE / 'completion-results.json').read_text())
    records = [r for r in done['results'] if r['F_index'] == 6]
    assert len(records) == 119 and all(r['status'] == 'COMPLETE' for r in records)
    expected = {i for i, r in enumerate(cover['representatives']) if r['F_index'] == 6}
    assert {r['source_index'] for r in records} == expected
    cases = [(r['source_index'], j, es) for r in records for j, es in enumerate(r['solutions'])]
    assert len(cases) == 5298
    return cover, cases

def graph(cover, case):
    si, sj, es = case
    rep = cover['representatives'][si]
    assert rep['F_index'] == 6
    g = [set() for _ in range(21)]
    def add(u, v):
        g[u].add(v)
        g[v].add(u)
    for u, v in rep['F_edges'] + es:
        add(u, v)
    for s, hs in enumerate(rep['singleton_hosts'], 7):
        for e in hs:
            add(s, e)
    assert all(len(g[s] & set(range(7))) == (2 if s < 14 else 1) for s in range(7, 21))
    assert all(len(g[u] & g[v]) <= 1 for u, v in itertools.combinations(range(21), 2))
    return g

def run():
    cover, cases = inputs()
    pins = {name: hashlib.sha256((SOURCE / name).read_bytes()).hexdigest()
            for name in ['results.json', 'completion-results.json']}
    launch = dict(stage='F6 high assignments', cases=5298, aggregate_seconds=30,
                  per_case_nodes=100000, source_pins=pins,
                  source_path=str(SOURCE), source_script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    with (OUT / 'high-launch.json').open('x') as f:
        json.dump(launch, f, indent=2)
    start = time.monotonic()
    deadline = start + 30
    rows = []
    for index, case in enumerate(cases):
        if time.monotonic() >= deadline:
            break
        g = graph(cover, case)
        allowed = [[d for d in range(7) if 7+d not in g[14+h] and not g[14+h] & g[7+d]] for h in range(7)]
        order = sorted(range(7), key=lambda h: (len(allowed[h]), h))
        pair = [-1] * 7
        solutions = []
        nodes = 0
        def visit(k, used):
            nonlocal nodes
            nodes += 1
            if nodes > 100000 or time.monotonic() >= deadline:
                raise TimeoutError
            if k == 7:
                solutions.append(pair.copy())
                return
            h = order[k]
            for d in allowed[h]:
                if not used & (1 << d):
                    pair[h] = d
                    visit(k+1, used | (1 << d))
        try:
            visit(0, 0)
            status = 'COMPLETE'
        except TimeoutError:
            status = 'UNKNOWN'
            solutions = []
        rows.append(dict(case_index=index, source_index=case[0], singleton_index=case[1],
                         status=status, nodes=nodes, pairings=solutions))
        if status == 'UNKNOWN':
            break
    summary = dict(total=len(cases), visited=len(rows), unvisited=len(cases)-len(rows),
                   counts=dict(collections.Counter(r['status'] for r in rows)),
                   pairings=sum(len(r['pairings']) for r in rows),
                   positive=sum(bool(r['pairings']) for r in rows),
                   seconds=time.monotonic()-start)
    (OUT / 'high-results.json').write_text(json.dumps(dict(summary=summary, results=rows))+'\n')
    print(json.dumps(summary))

if __name__ == '__main__':
    run()
