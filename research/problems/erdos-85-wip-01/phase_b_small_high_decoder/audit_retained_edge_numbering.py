"""Read retained input prefixes to bind all decoded edge IDs to actual clauses."""
import hashlib
import itertools
import json
from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1]/'sat49'))
import verify_small_high_sat_graph as decoder

ROOT = Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration/research/problems/erdos-85-wip-01')
OUT = Path(__file__).resolve().parent


def sha(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1048576), b''):
            h.update(block)
    return h.hexdigest()


def clauses(path):
    with path.open('rb') as stream:
        for raw in stream:
            if raw[:1] in (b'c', b'p') or not raw.strip():
                continue
            values = tuple(map(int, raw.split()))
            assert values[-1] == 0 and 0 not in values[:-1]
            yield values[:-1]


def main():
    h3 = json.loads((ROOT/'phase_b_h1_h3/h3-inputs.json').read_text())['instances']
    h5 = json.loads((ROOT/'phase_b_h5_h7/h5-inventory.json').read_text())['bases']
    rows = [(3, i, Path(r['cnf_path']), r['cnf_sha256']) for i, r in enumerate(h3)]
    rows += [(5, int(name[-1]), Path(r['base']), r['base_sha256']) for name, r in h5.items()]
    results = []
    for high_count, profile, path, expected_sha in rows:
        assert sha(path) == expected_sha
        if high_count == 3:
            edges = list(itertools.combinations(range(high_count), 2))
            edges += [(high, low) for low in range(high_count, 49) for high in range(high_count)]
            edges += list(itertools.combinations(range(high_count, 49), 2))
        else:
            edges = list(itertools.combinations(range(49), 2))
        mapping = {edge: i+1 for i, edge in enumerate(edges)}
        assert decoder.edge_variables(high_count) == {e: n for e, n in mapping.items() if e[0] >= high_count}
        supports = decoder.supports(high_count, profile)
        actual = clauses(path)
        count = 0
        for pair in itertools.combinations(range(high_count), 2):
            assert next(actual) == (-mapping[pair],)
            count += 1
        for low in range(high_count, 49):
            for high in range(high_count):
                literal = mapping[(high, low)] * (1 if high in supports[low] else -1)
                assert next(actual) == (literal,)
                count += 1
        fixed_units = count
        seen = set()
        for right in range(1, 49):
            others = [w for w in range(49) if w not in (0, right)]
            for first, second in itertools.combinations(others, 2):
                edges = [(0, first), tuple(sorted((right, first))),
                         (0, second), tuple(sorted((right, second)))]
                expected = tuple(-mapping[e] for e in edges)
                assert next(actual) == expected, (high_count, profile, count)
                count += 1
                seen.update(map(abs, expected))
        assert seen == set(range(1, 1177))
        results.append({'high_count': high_count, 'profile': profile, 'path': str(path),
                        'cnf_sha256': expected_sha, 'fixed_units_checked': fixed_units,
                        'c4_prefix_clauses_checked': count-fixed_units,
                        'edge_variables_bound': len(seen)})
    h7path = ROOT/'phase_b_h5_h7/h7-inventory.json'
    h7 = json.loads(h7path.read_text())
    variables = decoder.edge_variables(7)
    h7base = Path(h7['base']['path'])
    assert sha(h7base) == h7['base']['sha256']
    actual = clauses(h7base)
    for _ in range(720804-687260):
        next(actual)
    fixed = {(h, low) for low, support in decoder.supports(7, 0).items() for h in support}
    def status(a, b):
        edge = tuple(sorted((a, b)))
        return 0 if edge in fixed else variables.get(edge)
    c4_count = 0
    seen = set()
    for a, b in itertools.combinations(range(49), 2):
        others = [v for v in range(49) if v not in (a, b)]
        for x, y in itertools.combinations(others, 2):
            values = [status(a, x), status(b, x), status(a, y), status(b, y)]
            if None in values:
                continue
            expected = tuple(-v for v in values if v)
            assert next(actual) == expected, ('H7 C4 clause', c4_count)
            seen.update(map(abs, expected))
            c4_count += 1
    assert c4_count == 687260 and seen == set(range(1, 862))
    assert next(actual, None) is None
    for row in h7['mapping']:
        expected = [variables[(7+a, 7+b)]*(1 if row['mask'] >> i & 1 else -1)
                    for i, (a, b) in enumerate(itertools.combinations(range(7), 2))]
        assert row['units'] == expected
    report = {'scope': 'Actual H3/H5 fixed-unit and edge-ID prefix audit; H7 complete C4 block and all43 empty-cube unit maps. No SAT model or solver run.',
              'h3_h5': results, 'h7_cube_rows_checked': len(h7['mapping']),
              'h7_c4_clauses_checked': c4_count, 'h7_edge_variables_bound': len(seen),
              'h7_inventory_sha256': sha(h7path)}
    (OUT/'edge-numbering-audit.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report))


if __name__ == '__main__':
    main()
