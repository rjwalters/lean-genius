#!/usr/bin/env python3
"""CNF instances for the 78 reviewed q=8 [5,3] C5 carrier orbits."""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from pathlib import Path

from cnf_nonbip_mixed_53_exterior_carrier import (
    LARGE, ORDER, build_core, defect_var, dimacs, edge_var,
    parse_kissat_model, verify_core,
)
from enumerate_nonbip_mixed_53_c5_carrier_orbits import canonical, valid


N = 5


def representatives() -> list[tuple[tuple[int, ...], tuple[int, ...]]]:
    return sorted({canonical(h, r)
                   for h in itertools.product((0, 1), repeat=N)
                   for r in itertools.product((0, 1), repeat=N)
                   if valid(h, r)})


def exterior_sets(r: tuple[int, ...]) -> list[set[int]]:
    """Canonical five size-three fibers with chord overlaps encoded by r."""
    sets = [set() for _ in range(N)]
    label = LARGE
    for i, bit in enumerate(r):
        if bit:
            sets[i].add(label)
            sets[(i + 2) % N].add(label)
            label += 1
    for i in range(N):
        while len(sets[i]) < 3:
            sets[i].add(label)
            label += 1
    assert label <= ORDER
    assert all(len(s) == 3 for s in sets)
    assert all(not (sets[i] & sets[(i + 1) % N]) for i in range(N))
    assert all(bool(sets[i] & sets[(i + 2) % N]) == bool(r[i])
               for i in range(N))
    assert all(len(sets[i] & sets[(i + 2) % N]) <= 1 for i in range(N))
    return sets


def build(orbit_index: int):
    reps = representatives()
    if not 0 <= orbit_index < len(reps):
        raise ValueError(f"orbit index must lie in 0..{len(reps)-1}")
    h, r = reps[orbit_index]
    cnf = build_core()
    fibers = exterior_sets(r)

    # The named vertices 0..4 induce a C5 in the defect graph.
    for i in range(N):
        u, v = sorted((i, (i + 1) % N))
        cnf.add(defect_var(cnf, u, v))
        a = edge_var(cnf, u, v)
        cnf.add(a if h[i] else -a)
        u, v = sorted((i, (i + 2) % N))
        cnf.add(-defect_var(cnf, u, v))

    # Small-shore label symmetry canonically fixes the five carrier fibers.
    for i in range(N):
        for f in range(LARGE, ORDER):
            a = edge_var(cnf, i, f)
            cnf.add(a if f in fibers[i] else -a)
    return cnf, h, r, fibers


def verify_model(cnf, values: dict[int, bool], h: tuple[int, ...],
                 r: tuple[int, ...], fibers: list[set[int]]) -> dict[str, object]:
    sets, _, defect = verify_core(cnf, values)
    for i in range(N):
        u, v = sorted((i, (i + 1) % N))
        assert defect[u, v]
        assert (v in sets[u]) == bool(h[i])
        u, v = sorted((i, (i + 2) % N))
        assert not defect[u, v]
        assert bool((sets[i] & sets[(i + 2) % N]) & set(range(LARGE, ORDER))) == bool(r[i])
        assert sets[i] & set(range(LARGE, ORDER)) == fibers[i]
    neighbors = [sorted(row) for row in sets]
    raw = json.dumps(neighbors, separators=(",", ":")).encode()
    return {"model_sha256": hashlib.sha256(raw).hexdigest(),
            "carrier_profile": sorted((sum(f in s for s in fibers)
                                       for f in range(LARGE, ORDER)), reverse=True)}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--orbit-index", type=int, required=True)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--verify-model", type=Path)
    args = parser.parse_args()
    cnf, h, r, fibers = build(args.orbit_index)
    payload = dimacs(cnf)
    reps = representatives()
    report: dict[str, object] = {
        "orbit_index": args.orbit_index,
        "orbit_count": len(reps),
        "h": h,
        "r": r,
        "variables": cnf.next_var - 1,
        "clauses": len(cnf.clauses),
        "sha256": hashlib.sha256(payload).hexdigest(),
    }
    if args.output is not None:
        args.output.write_bytes(payload)
        report["output"] = str(args.output)
    if args.verify_model is not None:
        report.update(verify_model(cnf, parse_kissat_model(args.verify_model),
                                   h, r, fibers))
        report["model_verified"] = True
    print(json.dumps(report, sort_keys=True))


if __name__ == "__main__":
    main()
