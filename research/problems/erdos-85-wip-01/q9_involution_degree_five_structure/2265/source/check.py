import hashlib
import itertools
import json
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent

def run():
    for name, digest in json.loads((ROOT / 'input-pins.json').read_text()).items():
        assert hashlib.sha256(Path(name).read_bytes()).hexdigest() == digest, name
    graphs = json.loads((ROOT / 'representatives.json').read_text())
    retained = []
    counts = Counter()
    checks = 0
    for index, graph in enumerate(graphs):
        adj = [set() for _ in range(10)]
        for u, v in graph['edges']:
            assert u != v and v not in adj[u]
            adj[u].add(v)
            adj[v].add(u)
        assert all(len(a) == 3 for a in adj)
        assert all(len(adj[u] & adj[v]) <= 1 for u, v in itertools.combinations(range(10), 2))
        triangles = [list(t) for t in itertools.combinations(range(10), 3)
                     if all(v in adj[u] for u, v in itertools.combinations(t, 2))]
        assert triangles == graph['triangles']
        for subset in itertools.combinations(range(10), 4):
            checks += 1
            P = set(subset)
            M = set(range(10)) - P
            degree = [len(a & P) for a in adj]
            if sorted(degree) == [1]*9 + [3]:
                special = [v for v in range(10) if degree[v] == 3]
                kind = 'one221'
                # An actual 221 group covers R, hence meets the central orbit.
                if special[0] not in P:
                    continue
            elif sorted(degree) == [1]*8 + [2]*2:
                special = [v for v in range(10) if degree[v] == 2]
                kind = 'two211'
            else:
                continue
            counts[f'{len(triangles)}_triangles_{kind}'] += 1
            row = dict(graph_index=index, P=sorted(P), special=special, kind=kind)
            if kind == 'two211':
                assert set(special) <= M
                assert all(len(adj[v] & P) == 1 for v in P)
                assert sorted(len(adj[v] & M) for v in M) == [1,1,2,2,2,2]
                path = [special[0]]
                while len(path) < 6:
                    nxt = (adj[path[-1]] & M) - set(path)
                    assert len(nxt) == 1
                    path.append(next(iter(nxt)))
                assert path[-1] == special[1] and set(path) == M
                row['M_path'] = path
                assert len(triangles) == 3
            retained.append(row)
    assert checks == 630
    assert len(retained) == 24
    assert dict(counts) == {'0_triangles_one221':10, '2_triangles_one221':4,
                            '3_triangles_one221':1, '3_triangles_two211':9}
    return dict(marked_pairs_checked=checks, counts=dict(counts), retained=retained,
                surviving_marked_pairs=9, scope='Necessary fixed-graph restriction only')

if __name__ == '__main__':
    print(json.dumps(run(), indent=2))
