#!/usr/bin/env python3
"""Independent generator-graph audit of the 1,294 -> 63 orbit quotient.

Unlike stage1_canonicalize.py, this never enumerates all 12,288 group words
and never calls its `canon`.  It normalizes copy order, builds graph edges for
eight explicit generators, finds connected components, and compares component
minima and raw-record weights with the durable orbit artifact.

The original 1,294-record artifact intentionally fails this audit: an S4
generator image is valid but absent because the CP-SAT difference auxiliary
was incorrectly bounded by `[-11,11]` instead of its true `[-22,22]` range.
Keep this failure as a regression gate for the corrected enumeration.
"""

from collections import Counter
import hashlib
import json
from itertools import combinations
import sys

from hlift_witness import validate_witness

SOL_SHA = "05f2d5d613b283ea81aabb318cf283bc6a2f22257c13d8344d249a3b8b575f5d"
COMPS = range(4)


def links(omit):
    return [e for e in COMPS if e != omit]


def raw_to_wit(raw):
    wit = {}
    for key, value in raw.items():
        omit, copy, comp = map(int, key.split(","))
        wit.setdefault((omit, copy), {})[comp] = value
    return validate_witness(wit)


def normalize(wit):
    out = {}
    for omit in COMPS:
        vectors = []
        L = links(omit)
        for copy in range(4):
            row = wit[omit, copy]
            base = row[L[0]]
            vectors.append(tuple((row[e] - base) % 12 for e in L))
        out[str(omit)] = sorted(vectors)
    return json.dumps(out, separators=(",", ":"), sort_keys=True)


def decode(normalized):
    doc = json.loads(normalized)
    return {(omit, copy): {e: value for e, value in zip(links(omit), vector)}
            for omit in COMPS
            for copy, vector in enumerate(doc[str(omit)])}


def transform(wit, sigma, rotations, reflect):
    rows = {i: [] for i in COMPS}
    for (omit, _copy), row in wit.items():
        target = {}
        for comp, value in row.items():
            new_comp = sigma[comp]
            value = (-value) % 12 if reflect else value
            target[new_comp] = (value + rotations[new_comp]) % 12
        rows[sigma[omit]].append(target)
    # Copies are unlabeled under the residual symmetry; normalization sorts.
    provisional = {}
    for omit in COMPS:
        for copy, row in enumerate(rows[omit]):
            provisional[omit, copy] = row
    return normalize(provisional)


GENERATORS = [
    ((1, 0, 2, 3), (0, 0, 0, 0), False),
    ((0, 2, 1, 3), (0, 0, 0, 0), False),
    ((0, 1, 3, 2), (0, 0, 0, 0), False),
] + [
    (tuple(COMPS), tuple(3 if i == k else 0 for i in COMPS), False)
    for k in COMPS
] + [(tuple(COMPS), (0, 0, 0, 0), True)]


def main():
    if len(sys.argv) != 3:
        raise SystemExit(f"usage: {sys.argv[0]} SOLUTIONS_JSON ORBITS_JSON")
    sol_bytes = open(sys.argv[1], "rb").read()
    assert hashlib.sha256(sol_bytes).hexdigest() == SOL_SHA
    solutions = json.loads(sol_bytes)["solutions"]
    assert len(solutions) == 1294
    normalized = [normalize(raw_to_wit(raw)) for raw in solutions]
    weights = Counter(normalized)
    nodes = set(weights)
    print(f"raw {len(solutions)} normalized {len(nodes)}")

    adjacency = {node: set() for node in nodes}
    for node in nodes:
        wit = decode(node)
        validate_witness(wit)
        for generator_index, generator in enumerate(GENERATORS):
            image = transform(wit, *generator)
            if image not in nodes:
                raise AssertionError(
                    "generator image absent from claimed-complete source: "
                    f"generator={generator_index}; this usually indicates "
                    "a non-symmetric accidental constraint in enumeration")
            adjacency[node].add(image)
            adjacency[image].add(node)

    components = []
    unseen = set(nodes)
    while unseen:
        seed = min(unseen)
        stack = [seed]
        component = set()
        while stack:
            node = stack.pop()
            if node in component:
                continue
            component.add(node)
            stack.extend(adjacency[node] - component)
        unseen -= component
        components.append(component)
    components.sort(key=min)

    orbit_bytes = open(sys.argv[2], "rb").read()
    orbit_sha = hashlib.sha256(orbit_bytes).hexdigest()
    artifact = json.loads(orbit_bytes)
    artifact_reps = artifact["representatives"]
    # Normalize whitespace/key formatting before comparing representations.
    expected_reps = [json.dumps(json.loads(rep), separators=(",", ":"),
                                sort_keys=True) for rep in artifact_reps]
    expected = {rep: multiplicity for rep, multiplicity in
                zip(expected_reps, artifact["multiplicities"])}
    actual = {min(component): sum(weights[node] for node in component)
              for component in components}
    assert artifact["orbit_count"] == len(components) == 63
    assert actual == expected
    assert sum(actual.values()) == 1294
    print(f"orbits 63 weights 1294 artifact_sha256 {orbit_sha}")
    print("ALL OK")


if __name__ == "__main__":
    main()
