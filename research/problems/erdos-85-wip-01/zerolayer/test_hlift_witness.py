#!/usr/bin/env python3
"""Small positive/negative tests for hash-pinned fixed-WIT loading."""

import hashlib
import json
import os
import tempfile

from hlift_witness import load_orbit_witness, validate_witness

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

validate_witness(BASE)
rep = {str(o): [[BASE[o, j][e] for e in range(4) if e != o]
                for j in range(4)] for o in range(4)}
doc = {"orbit_count": 1, "representatives": [json.dumps(rep)]}
raw = json.dumps(doc, sort_keys=True).encode()
with tempfile.NamedTemporaryFile(delete=False) as handle:
    handle.write(raw)
    path = handle.name
try:
    wit, provenance = load_orbit_witness(path, hashlib.sha256(raw).hexdigest(), 0)
    assert wit == BASE and provenance["orbit_index"] == 0
    try:
        load_orbit_witness(path, "0" * 64, 0)
        raise AssertionError("bad hash accepted")
    except AssertionError as exc:
        assert "hash mismatch" in str(exc)
    bad = {key: dict(value) for key, value in BASE.items()}
    bad[0, 0][1] = 1
    try:
        validate_witness(bad)
        raise AssertionError("bad gauge accepted")
    except AssertionError as exc:
        assert "gauge fails" in str(exc)
finally:
    os.unlink(path)
print("ALL OK")
