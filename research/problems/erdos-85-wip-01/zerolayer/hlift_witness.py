#!/usr/bin/env python3
"""Load and validate a fixed stage-1 witness for the H-lift encoder."""

import hashlib
import json
from itertools import combinations

COMPS = range(4)
ORPHANS = [(i, j) for i in COMPS for j in range(4)]


def links(omit):
    return [e for e in COMPS if e != omit]


def validate_witness(wit):
    """Pure-Python validation of the complete gauge-fixed stage-1 model."""
    assert set(wit) == set(ORPHANS), "witness must contain exactly 16 orphans"
    for orphan in ORPHANS:
        expected = set(links(orphan[0]))
        assert set(wit[orphan]) == expected, f"bad links for orphan {orphan}"
        values = [wit[orphan][e] for e in links(orphan[0])]
        assert all(isinstance(v, int) and 0 <= v < 12 for v in values)
        assert values[0] == 0, f"first-link gauge fails at {orphan}"
        assert len({v % 3 for v in values}) == 3, \
            f"row residues not distinct at {orphan}"
    for omit in COMPS:
        second = links(omit)[1]
        values = [wit[omit, copy][second] for copy in range(4)]
        assert values == sorted(values), f"copy ordering fails for type {omit}"
    for o1, o2 in combinations(ORPHANS, 2):
        shared = sorted(set(wit[o1]) & set(wit[o2]))
        for e, f in combinations(shared, 2):
            delta = ((wit[o2][e] - wit[o1][e]) -
                     (wit[o2][f] - wit[o1][f])) % 12
            assert delta != 0, f"pair injectivity fails for {o1}, {o2}, {e}, {f}"
    return wit


def load_orbit_witness(path, expected_sha256, orbit_index):
    """Load one canonical representative from a hash-pinned orbit artifact."""
    raw = open(path, "rb").read()
    actual = hashlib.sha256(raw).hexdigest()
    assert actual == expected_sha256, \
        f"orbit artifact hash mismatch: expected {expected_sha256}, got {actual}"
    doc = json.loads(raw)
    reps = doc["representatives"]
    assert doc["orbit_count"] == len(reps)
    assert 0 <= orbit_index < len(reps), "orbit index out of range"
    rep = reps[orbit_index]
    rep = json.loads(rep) if isinstance(rep, str) else rep
    assert set(rep) == {str(i) for i in COMPS}
    wit = {}
    for omit in COMPS:
        vectors = rep[str(omit)]
        assert len(vectors) == 4
        L = links(omit)
        for copy, vector in enumerate(vectors):
            assert len(vector) == 3
            wit[omit, copy] = {e: value for e, value in zip(L, vector)}
    return validate_witness(wit), {
        "orbit_artifact_sha256": actual,
        "orbit_index": orbit_index,
        "orbit_count": len(reps),
    }
