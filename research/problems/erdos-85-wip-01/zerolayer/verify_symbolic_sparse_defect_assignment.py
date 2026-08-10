#!/usr/bin/env python3
"""Independently verify a SAT assignment for either local sparse-center CNF."""

import re
import sys

from hlift_witness import validate_witness
from verify_stage1_color_action import graphs, ORPHANS, N, vid


def assignment(path):
    text = open(path, encoding="utf-8", errors="replace").read()
    if "s SATISFIABLE" not in text:
        raise ValueError("solver output is not SATISFIABLE")
    values = set()
    for line in text.splitlines():
        if line.startswith("v "):
            values.update(int(token) for token in re.findall(r"-?\d+", line)
                          if int(token) > 0)
    return values


def main():
    true = assignment(sys.argv[1])
    variable = 0
    phases = {}
    for orphan in ORPHANS:
        for component in [e for e in range(4) if e != orphan[0]]:
            selected = []
            for phase in range(12):
                variable += 1
                if variable in true:
                    selected.append(phase)
            if len(selected) != 1:
                raise ValueError(f"bad phase one-hot {orphan},{component}")
            phases.setdefault(orphan, {})[component] = selected[0]
    validate_witness(phases)

    # Skip DELTA and SERVICE variables in their deterministic encoder order.
    delta_count = 0
    service_count = 0
    for i, left in enumerate(ORPHANS):
        for right in ORPHANS[i + 1:]:
            delta_count += 12 * len(set(phases[left]) & set(phases[right]))
            service_count += 12 * 12
    variable += delta_count + service_count
    selected = set()
    for vertex in range(N):
        variable += 1
        if variable in true:
            selected.add(vertex)

    A = graphs(phases)
    center, forward = vid((0, 0), 0), vid((0, 0), 1)
    wrong_color = "--wrong-color-overlap" in sys.argv
    if len(selected) != 13 or center in selected or (
            not wrong_color and forward not in selected):
        raise ValueError("bad candidate size or pin")
    for pair in A:
        if pair <= selected:
            raise ValueError(f"candidate is not A-independent: {pair}")
    center_neighbors = {next(iter(pair - {center})) for pair in A
                        if center in pair}
    overlap = selected & center_neighbors
    if not wrong_color and overlap != {forward}:
        raise ValueError("forward defect neighbor is not unique overlap")
    if wrong_color:
        if len(overlap) != 1:
            raise ValueError("candidate does not have a unique overlap")
        unique = next(iter(overlap))
        orphan = ORPHANS[unique // 12]
        if 1 in phases[orphan] and (
                unique % 12 + phases[orphan][1]) % 3 == 0:
            raise ValueError("unique overlap has the center's paired color")
    counts = [0, 0, 0]
    for vertex in selected:
        orphan = ORPHANS[vertex // 12]
        if 1 in phases[orphan]:
            counts[(vertex % 12 + phases[orphan][1]) % 3] += 1
    if counts != [4, 4, 4]:
        raise ValueError(f"bad paired-component color counts: {counts}")
    print("SYMBOLIC SPARSE DEFECT ASSIGNMENT VERIFIED")


if __name__ == "__main__":
    main()
