"""Exact abstract trade check; no ambient graph completion is claimed."""
import hashlib
import json
from pathlib import Path

def check(q):
    assert q >= 8 and q & (q - 1) == 0
    m, n = q // 2, q * (q - 1)
    # Each point is represented by its negative and positive incident blocks.
    U = [(frozenset((i, i+1)), frozenset((i, i+1)))
         for i in range(0, q, 2)]
    U += [(frozenset((i,)), frozenset((i ^ d,)))
          for d in range(2, m+1) for i in range(q)]
    X = [(frozenset((i,)), frozenset((i ^ d,)))
         for d in range(m+1, q-1) for i in range(q)]
    # Two additional negative incidences per row, on distinct pair matchings.
    # Their positive load is zero, so their local defect is two.
    X += [(frozenset((i, i ^ d)), frozenset())
          for d in (2,4) for i in range(q) if i < (i ^ d)]
    X += [(frozenset(), frozenset())] * (n//2-len(X))
    assert len(U) == len(X) == n//2
    assert all(len(a) == len(b) for a,b in U)
    assert all(len(a) >= len(b) for a,b in X)
    assert sum(len(a)-len(b) for a,b in X) == 2*q
    for i in range(q):
        assert sum(i in a for a,b in U) == m
        assert sum(i in b for a,b in U) == m
        assert sum(i in a for a,b in X) == m
        assert sum(i in b for a,b in X) == m-2
    # All positive weights are one; sum weights = |Z| = q.
    for i in range(q):
        for j in range(q):
            assert sum(i in a and j in b for a,b in U+X) <= 1
        for j in range(i):
            assert sum(i in a and j in a for a,b in U+X) <= 1
            assert sum(i in b and j in b for a,b in U+X) <= 1
    cu = sum(len(a)*len(b) for a,b in U)
    cx = sum(len(a)*len(b) for a,b in X)
    assert cu == q*(m+1) and cx == q*(m-2)
    assert cu+cx == q*(q-1) <= q*q
    profile = [0]*q + [2]*q + [1]*(n-2*q)
    assert len(profile) == sum(profile) == n
    assert sum((r-1)**2 for r in profile) == 2*q
    return dict(q=q,z=q,bound=q-1,shore_size=n//2,
                U_collision=cu,X_collision=cx,reuse_charge=cu-m*q,
                total_collision=cu+cx,pair_capacity=q*q,cut=2*q)

if __name__ == '__main__':
    result = dict(status='PASS', scope='Fixed cardinalities plus generic trade '
                  'hypotheses and same-sign linearity; not an ambient endpoint',
                  cases=[check(q) for q in (8,16,32,64)],
                  checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    Path(__file__).with_name('result.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
