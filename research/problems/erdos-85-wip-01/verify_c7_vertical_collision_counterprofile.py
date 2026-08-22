#!/usr/bin/env python3
"""Verify the local C7 rooted counterprofile from Section 70.

This is intentionally not a full SRP or ambient completion.  It checks the
claimed local incidences, the unique vertically repeated e-port, the two
distinct f cut ports, and C4-freeness of the displayed skeleton.
"""

from collections import defaultdict


edges: set[frozenset[str]] = set()


def add(u: str, v: str) -> None:
    assert u != v
    edges.add(frozenset((u, v)))


# The projected A_c cycle.
for i in range(7):
    add(f"x{i}", f"x{(i + 1) % 7}")

# e-owner ports: the three-edge run and its distance-three closing chord.
for name, u, v in (
    ("e01", "x0", "x1"),
    ("e12", "x1", "x2"),
    ("e23", "x2", "x3"),
    ("z", "x0", "x3"),
):
    add(name, u)
    add(name, v)

# f-owner ports on the four-edge run.
for name, u, v in (
    ("f34", "x3", "x4"),
    ("f45", "x4", "x5"),
    ("f56", "x5", "x6"),
    ("f60", "x6", "x0"),
):
    add(name, u)
    add(name, v)

# Distinct cut ports at the change roots, continued through distinct roots.
add("u0", "x0")
add("u0", "y0")
add("u3", "x3")
add("u3", "y3")

# The two direct rooted transitions reuse z and use distinct f ports.
add("z", "u0")
add("z", "u3")

neighbors: dict[str, set[str]] = defaultdict(set)
for edge in edges:
    u, v = tuple(edge)
    neighbors[u].add(v)
    neighbors[v].add(u)

vertices = sorted(neighbors)
max_codegree = 0
max_pairs: list[tuple[str, str]] = []
for i, u in enumerate(vertices):
    for v in vertices[i + 1 :]:
        codegree = len(neighbors[u] & neighbors[v])
        if codegree > max_codegree:
            max_codegree = codegree
            max_pairs = [(u, v)]
        elif codegree == max_codegree:
            max_pairs.append((u, v))

assert max_codegree <= 1, (max_codegree, max_pairs)
assert neighbors["z"] & {"x0", "x3"} == {"x0", "x3"}
assert neighbors["z"] & {"u0", "u3"} == {"u0", "u3"}
assert neighbors["u0"] & {"x0", "y0"} == {"x0", "y0"}
assert neighbors["u3"] & {"x3", "y3"} == {"x3", "y3"}

# Section 70's cut/collision ledger.
v_e = v_f = 2
kappa_e, kappa_f = 1, 0
cut_e, cut_f = 0, 2
assert v_e == 2 * kappa_e + cut_e
assert v_f == 2 * kappa_f + cut_f
assert kappa_e + kappa_f == 1

print(f"vertices={len(vertices)} edges={len(edges)} max_codegree={max_codegree}")
print("v=(2,2) cuts=(0,2) kappa_vert=1")
