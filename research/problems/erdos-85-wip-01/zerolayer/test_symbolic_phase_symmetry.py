#!/usr/bin/env python3
"""Check the constructive normalization behind symbolic phase symmetry."""

from itertools import product

from hlift_witness import validate_witness

BASE = {
 (0,0): {1:0, 2:4, 3:2}, (0,1): {1:0, 2:5, 3:4},
 (0,2): {1:0, 2:8, 3:1}, (0,3): {1:0, 2:10, 3:5},
 (1,0): {0:0, 2:2, 3:4}, (1,1): {0:0, 2:4, 3:5},
 (1,2): {0:0, 2:7, 3:11}, (1,3): {0:0, 2:11, 3:7},
 (2,0): {0:0, 1:5, 3:1}, (2,1): {0:0, 1:7, 3:2},
 (2,2): {0:0, 1:10, 3:8}, (2,3): {0:0, 1:11, 3:10},
 (3,0): {0:0, 1:1, 2:8}, (3,1): {0:0, 1:2, 2:1},
 (3,2): {0:0, 1:4, 2:5}, (3,3): {0:0, 1:8, 2:10},
}
COMPS = range(4)
def links(omit): return [e for e in COMPS if e != omit]


def rotate_and_regauge(wit, rotations):
    out = {}
    for (omit, copy), row in wit.items():
        first = links(omit)[0]
        out[omit, copy] = {
            e: (value + rotations[e] - rotations[first]) % 12
            for e, value in row.items()}
    return out


def normalize(wit):
    # Choose relative used-component rotations constructively.
    rotations = {1: 0}
    value = wit[0, 0][2]
    rotations[2] = (value % 3 - value) % 12
    partially = rotate_and_regauge(wit, {0: 0, 1: 0, 2: rotations[2], 3: 0})
    # After the rotation fixing component two, copy sorting chooses this row;
    # use the still-free component-three rotation to normalize its third phase.
    anchor0 = min(range(4), key=lambda copy: partially[0, copy][2])
    value = partially[0, anchor0][3]
    rotations[3] = (value % 3 - value) % 12
    # The remaining relative rotation fixes the sorted type-one anchor on its
    # second link (component two).
    value = wit[1, 0][2]
    target = value % 3
    rotations[0] = (value + rotations[2] - target) % 12
    rotated = rotate_and_regauge(wit, rotations)
    out = {}
    for omit in COMPS:
        second = links(omit)[1]
        rows = sorted((rotated[omit, copy] for copy in range(4)),
                      key=lambda row: row[second])
        for copy, row in enumerate(rows):
            out[omit, copy] = row
    validate_witness(out)
    assert all(out[omit, copy][links(omit)[1]] <=
               out[omit, copy + 1][links(omit)[1]]
               for omit in COMPS for copy in range(3))
    assert all(out[orphan][component] < 3 for orphan, component in
               [((0, 0), 2), ((0, 0), 3), ((1, 0), 2)])
    return out


canonical = normalize(BASE)
for rotations in product((0, 3, 6, 9), repeat=4):
    transformed = rotate_and_regauge(BASE, dict(enumerate(rotations)))
    assert normalize(transformed) == canonical
print("ALL OK")
