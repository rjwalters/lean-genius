"""Bounded U-only audit; no cross-edge or resolution enumeration."""
from itertools import combinations, permutations, product
from pathlib import Path
import json

MASKS = (129,257,513,34,66,514,20,68,260,24,40,136,528,288,192)
EDGES = list(combinations(range(5), 2))

def adjacency(a, b, pi, missing):
    rows = [0] * 15
    def add(i, j):
        rows[i] |= 1 << j
        rows[j] |= 1 << i
    for k, mask in enumerate((129, a, b)):
        for bit, (i, j) in enumerate(EDGES):
            if mask >> bit & 1:
                add(5*k+i, 5*k+j)
    for i in range(5):
        add(i, 5+i)
        add(i, 10+i)
        if i != missing:
            add(5+i, 10+pi[i])
    return rows

def audit(deficient):
    counts = dict(raw=0, valid=0, large_rows_reject=0, triangle_reject=0, either_reject=0)
    examples = []
    for a, b, pi, d in product(MASKS, MASKS, permutations(range(5)), range(5) if deficient else [None]):
        counts['raw'] += 1
        rows = adjacency(a, b, pi, d)
        if any((rows[i] & rows[j]).bit_count() > 1 for i, j in combinations(range(15), 2)):
            continue
        counts['valid'] += 1
        large = sum(r.bit_count() <= 1 for r in rows) > 1
        low = [i for i, row in enumerate(rows) if row.bit_count() <= 2]
        triangle = next((t for t in combinations(low, 3)
            if all(rows[i] & rows[j] for i, j in combinations(t, 2))), None)
        counts['large_rows_reject'] += large
        counts['triangle_reject'] += triangle is not None
        counts['either_reject'] += large or triangle is not None
        if triangle is not None and not examples:
            examples.append(dict(masks=[129,a,b], permutation=pi, missing=d, triangle=triangle))
    counts['survivors'] = counts['valid'] - counts['either_reject']
    return dict(counts=counts, first_triangle_example=examples[0])

if __name__ == '__main__':
    result = dict(full=audit(False), deficient=audit(True),
        scope='Python U-only obstruction counts; not a Lean count theorem or whole-graph rejection')
    Path(__file__).with_name('counts.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))
