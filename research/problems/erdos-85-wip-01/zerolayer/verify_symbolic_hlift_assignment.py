#!/usr/bin/env python3
"""Independently verify SAT for the symbolic full-class H-lift encoding."""

from itertools import combinations
import sys

from hlift_witness import validate_witness
from verify_hlift_assignment import parse_kissat_assignment, verify_structure

COMPS = range(4)
ORPHANS = [(omit, copy) for omit in COMPS for copy in range(4)]
OIDX = {orphan: index for index, orphan in enumerate(ORPHANS)}
N = 192
EDGE_COUNT = N * (N - 1) // 2


def links(orphan):
    return [e for e in COMPS if e != orphan[0]]


def phase_variable_map():
    variable = EDGE_COUNT
    mapping = {}
    for orphan in ORPHANS:
        for component in links(orphan):
            for phase in range(12):
                variable += 1
                mapping[orphan, component, phase] = variable
    return mapping, variable


def extract_witness(values):
    mapping, _last = phase_variable_map()
    witness = {}
    for orphan in ORPHANS:
        row = {}
        for component in links(orphan):
            selected = [phase for phase in range(12)
                        if values.get(mapping[orphan, component, phase])]
            if len(selected) != 1:
                raise ValueError(f"phase one-hot failure at {orphan},{component}: "
                                 f"{selected}")
            row[component] = selected[0]
        witness[orphan] = row
    return validate_witness(witness)


def fixed_graphs(witness):
    def vid(orphan, x):
        return 12 * OIDX[orphan] + x % 12
    defect = {frozenset((vid(orphan, x), vid(orphan, x + 1)))
              for orphan in ORPHANS for x in range(12)}
    service = set()
    for o1, o2 in combinations(ORPHANS, 2):
        shared = sorted(set(witness[o1]) & set(witness[o2]))
        deltas = [(witness[o1][e] - witness[o2][e]) % 12 for e in shared]
        if len(deltas) != len(set(deltas)):
            raise ValueError(f"pair-injectivity failure at {o1},{o2}")
        for x in range(12):
            for delta in deltas:
                pair = frozenset((vid(o1, x), vid(o2, x + delta)))
                if pair in service:
                    raise ValueError(f"duplicate service edge {pair}")
                service.add(pair)
    if len(defect) != 192 or len(service) != 3168 or defect & service:
        raise ValueError("invalid reconstructed D/S sizes or overlap")
    return defect, service


def self_test():
    baseline = {
     (0,0): {1:0, 2:4, 3:2}, (0,1): {1:0, 2:5, 3:4},
     (0,2): {1:0, 2:8, 3:1}, (0,3): {1:0, 2:10, 3:5},
     (1,0): {0:0, 2:2, 3:4}, (1,1): {0:0, 2:4, 3:5},
     (1,2): {0:0, 2:7, 3:11}, (1,3): {0:0, 2:11, 3:7},
     (2,0): {0:0, 1:5, 3:1}, (2,1): {0:0, 1:7, 3:2},
     (2,2): {0:0, 1:10, 3:8}, (2,3): {0:0, 1:11, 3:10},
     (3,0): {0:0, 1:1, 2:8}, (3,1): {0:0, 1:2, 2:1},
     (3,2): {0:0, 1:4, 2:5}, (3,3): {0:0, 1:8, 2:10},
    }
    mapping, last = phase_variable_map()
    values = {variable: False for variable in range(EDGE_COUNT + 1, last + 1)}
    for (orphan, component), phase in [
            ((orphan, component), phase)
            for orphan, row in baseline.items()
            for component, phase in row.items()]:
        values[mapping[orphan, component, phase]] = True
    assert extract_witness(values) == baseline
    defect, service = fixed_graphs(baseline)
    assert (len(defect), len(service), len(defect | service)) == (192, 3168, 3360)
    values[mapping[(0, 0), 1, 0]] = False
    try:
        extract_witness(values)
        raise AssertionError("missing phase accepted")
    except ValueError as exc:
        assert "one-hot failure" in str(exc)
    print("SELF-TEST OK")


def main():
    if len(sys.argv) == 2 and sys.argv[1] == "--self-test":
        self_test()
        return
    if len(sys.argv) != 2:
        raise SystemExit(f"usage: {sys.argv[0]} KISSAT_LOG | --self-test")
    phase_map, last_phase = phase_variable_map()
    assignment = parse_kissat_assignment(sys.argv[1], last_phase)
    witness = extract_witness(assignment)
    defect, service = fixed_graphs(witness)
    all_pairs = [frozenset(pair) for pair in combinations(range(N), 2)]
    edges = []
    for variable in range(1, EDGE_COUNT + 1):
        if variable not in assignment:
            raise ValueError(f"missing edge variable {variable}")
        edges.append(assignment[variable])
    result = verify_structure(N, defect | service, all_pairs, edges, 13, 264)
    print("VERIFIED RELAXATION_SAT", result)
    print("WITNESS", witness)


if __name__ == "__main__":
    main()
