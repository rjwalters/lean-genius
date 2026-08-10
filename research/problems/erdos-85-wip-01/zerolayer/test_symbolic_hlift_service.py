#!/usr/bin/env python3
"""Independent semantic test for symbolic service adjacency orientation."""

from itertools import combinations

from hlift_witness import validate_witness

WIT = {
 (0,0): {1:0, 2:4, 3:2}, (0,1): {1:0, 2:5, 3:4},
 (0,2): {1:0, 2:8, 3:1}, (0,3): {1:0, 2:10, 3:5},
 (1,0): {0:0, 2:2, 3:4}, (1,1): {0:0, 2:4, 3:5},
 (1,2): {0:0, 2:7, 3:11}, (1,3): {0:0, 2:11, 3:7},
 (2,0): {0:0, 1:5, 3:1}, (2,1): {0:0, 1:7, 3:2},
 (2,2): {0:0, 1:10, 3:8}, (2,3): {0:0, 1:11, 3:10},
 (3,0): {0:0, 1:1, 2:8}, (3,1): {0:0, 1:2, 2:1},
 (3,2): {0:0, 1:4, 2:5}, (3,3): {0:0, 1:8, 2:10},
}
validate_witness(WIT)
orphans = sorted(WIT)
index = {orphan: i for i, orphan in enumerate(orphans)}
def vid(orphan, x): return 12 * index[orphan] + x % 12

service = set()
for o1, o2 in combinations(orphans, 2):
    shared = sorted(set(WIT[o1]) & set(WIT[o2]))
    deltas = [(WIT[o1][e] - WIT[o2][e]) % 12 for e in shared]
    assert len(deltas) == len(set(deltas))
    for x in range(12):
        for delta in deltas:
            pair = frozenset((vid(o1, x), vid(o2, x + delta)))
            assert pair not in service
            service.add(pair)

defect = {frozenset((vid(o, x), vid(o, x + 1)))
          for o in orphans for x in range(12)}
assert len(service) == 3168 and len(defect) == 192
assert service.isdisjoint(defect)
degrees = [0] * 192
for pair in service:
    for vertex in pair:
        degrees[vertex] += 1
assert set(degrees) == {33}
print("ALL OK")
