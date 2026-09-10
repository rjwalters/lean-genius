"""Exact local capacity refinement of the reviewed fixed-psi7 compression test."""
import json
from pathlib import Path
from verify_q7_h7_empty_compression_cuts import main as verify_compression

verify_compression()
witness = json.loads(Path(__file__).with_name('q7_h7_empty_compression_cuts.json').read_text())
expected = [
    [0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 16, 17, 18, 20, 32, 33, 34, 36],
    [0, 1, 2, 3, 4, 5, 8, 9, 10, 12, 16, 17, 18, 20, 24, 26, 28, 32, 33, 34, 36, 48, 50, 52],
]
for i, shape in enumerate(witness['shapes']):
    degree = [0] * 7
    for u, v in shape['shape']:
        degree[u] += 1
        degree[v] += 1
    capacity = [7 - 2 * d for d in degree]
    retained = []
    rejected = []
    for case in shape['cases']:
        if case['status'] != 'positive_definite':
            continue
        pair_degree = [0] * 7
        for k, (u, v) in enumerate(shape['allowed']):
            if case['mask'] >> k & 1:
                pair_degree[u] += 1
                pair_degree[v] += 1
        if all(d <= c for d, c in zip(pair_degree, capacity)):
            retained.append(case['mask'])
        else:
            rejected.append(case['mask'])
    assert retained == expected[i]
    assert len(rejected) == [7, 6][i]
    triples = [mask for mask in retained if mask.bit_count() == 3]
    assert triples == [[], [26, 28, 50, 52]][i]
    print('PASS shape', 'AB'[i], 'retained', len(retained), 'new cuts', len(rejected), 'triple masks', triples)
print('Necessary local-capacity plus fixed-spectrum compression only; no graph realization or endpoint exclusion.')
