#!/usr/bin/env python3
"""Test the local exceptional-hole six-pack obstruction in the q=9 design.

An exceptional ordinary B0 row is a selected rainbow hole triple.  Its six
residual neighbors must consist of three selected rainbow triples and one
marked-support pair of each missing color.  The two Gram laws proved in Lean
force these six U1 blocks to be pairwise disjoint and every one of them to
have no K-edge to the hole triple.  This script asks whether even one such
local configuration can occur in the full outer 24-point design.

Exploratory only: UNSAT still requires an independently checked certificate
or a kernel proof.
"""

from __future__ import annotations

import argparse
import time
from pathlib import Path
import sys

from z3 import And, Bool, If, Implies, Not, Or, Sum, sat, unknown

sys.path.insert(0, str(Path(__file__).resolve().parent))
import q9_three_high_u1_design_sat as outer


def exactly_one(xs):
    return Sum([If(x, 1, 0) for x in xs]) == 1


def build(branch: int, timeout_ms: int, all_holes: bool,
          diagonal_rows: bool = False, all_regular_classes: bool = False):
    solver, data = outer.build(branch, timeout_ms)
    triples = data["triples"]
    pairs = list(data["marked_pairs"])
    pack_count = (2 if branch == 3 else 4) if all_holes else 1
    anchors = []
    for r in range(pack_count):
        anchor = {t: Bool(f"sixpack_{r}_anchor_{t[0]}_{t[1]}_{t[2]}")
                  for t in triples}
        triple_neighbor = {
            t: Bool(f"sixpack_{r}_triple_{t[0]}_{t[1]}_{t[2]}") for t in triples
        }
        pair_neighbor = {
            e: Bool(f"sixpack_{r}_pair_{e[0]}_{e[1]}") for e in pairs
        }
        anchors.append(anchor)
        solver.add(exactly_one(anchor.values()))
        for t in triples:
            solver.add(Implies(anchor[t], data["holes"][t]))
            solver.add(Implies(triple_neighbor[t], data["selected"][t]))
            solver.add(Not(And(anchor[t], triple_neighbor[t])))
        solver.add(Sum([If(q, 1, 0) for q in triple_neighbor.values()]) == 3)

        for e in pairs:
            solver.add(Implies(pair_neighbor[e], data["marked_pairs"][e]))
        for missing_color in range(3):
            group = [pair_neighbor[e] for e in pairs
                     if missing_color not in {outer.color(e[0]), outer.color(e[1])}]
            solver.add(exactly_one(group))

        # The six neighbor blocks are pairwise disjoint.
        neighbor_point = {}
        for b in range(outer.N):
            uses = ([triple_neighbor[t] for t in triples if b in t]
                    + [pair_neighbor[e] for e in pairs if b in e])
            solver.add(Sum([If(q, 1, 0) for q in uses]) <= 1)
            neighbor_point[b] = Or(uses)

        anchor_point = {
            b: Or([anchor[t] for t in triples if b in t]) for b in range(outer.N)
        }
        # Mixed Gram law: no K-edge joins the anchor block to a neighbor block.
        for a in range(outer.N):
            for b in range(a + 1, outer.N):
                solver.add(Implies(data["k"][outer.edge_key(a, b)],
                                   Not(Or(And(anchor_point[a], neighbor_point[b]),
                                          And(anchor_point[b], neighbor_point[a])))))
    if all_holes:
        for t in triples:
            solver.add(Sum([If(anchor[t], 1, 0) for anchor in anchors]) ==
                       If(data["holes"][t], 1, 0))
    if diagonal_rows:
        for r in range(8):
            anchor_block = {r, 8 + r, 16 + r}
            triple_neighbor = {
                t: Bool(f"diagonal_{r}_triple_{t[0]}_{t[1]}_{t[2]}")
                for t in triples
            }
            pair_neighbor = {
                e: Bool(f"diagonal_{r}_pair_{e[0]}_{e[1]}") for e in pairs
            }
            for t in triples:
                solver.add(Implies(triple_neighbor[t], data["selected"][t]))
                if set(t) == anchor_block:
                    solver.add(Not(triple_neighbor[t]))
            for e in pairs:
                solver.add(Implies(pair_neighbor[e], data["marked_pairs"][e]))
            triple_count = Sum([If(q, 1, 0) for q in triple_neighbor.values()])
            pair_hits = []
            all_neighbors = list(triple_neighbor.values()) + list(pair_neighbor.values())
            solver.add(Sum([If(q, 1, 0) for q in all_neighbors]) == 5)
            for missing_color in range(3):
                group = [pair_neighbor[e] for e in pairs
                         if missing_color not in {outer.color(e[0]), outer.color(e[1])}]
                hit = Sum([If(q, 1, 0) for q in group])
                solver.add(hit <= 1)
                pair_hits.append(If(hit == 0, 1, 0))
            solver.add(Sum(pair_hits) == triple_count - 2)
            neighbor_point = {}
            for b in range(outer.N):
                uses = ([triple_neighbor[t] for t in triples if b in t]
                        + [pair_neighbor[e] for e in pairs if b in e])
                solver.add(Sum([If(q, 1, 0) for q in uses]) <= 1)
                neighbor_point[b] = Or(uses)
            for a in anchor_block:
                for b in range(outer.N):
                    if a != b:
                        solver.add(Implies(data["k"][outer.edge_key(a, b)],
                                           Not(neighbor_point[b])))
    if all_regular_classes:
        for class_index in (1, 2):
            slot_count = 8 if branch == 3 else 7
            class_anchors = []
            for r in range(slot_count):
                anchor = {
                    t: Bool(f"regular_{class_index}_{r}_anchor_{t[0]}_{t[1]}_{t[2]}")
                    for t in triples
                }
                class_anchors.append(anchor)
                solver.add(exactly_one(anchor.values()))
                triple_neighbor = {
                    t: Bool(f"regular_{class_index}_{r}_triple_{t[0]}_{t[1]}_{t[2]}")
                    for t in triples
                }
                pair_neighbor = {
                    e: Bool(f"regular_{class_index}_{r}_pair_{e[0]}_{e[1]}")
                    for e in pairs
                }
                for t in triples:
                    solver.add(Implies(anchor[t], data["classes"][class_index][t]))
                    solver.add(Implies(triple_neighbor[t], data["selected"][t]))
                    solver.add(Not(And(anchor[t], triple_neighbor[t])))
                for e in pairs:
                    solver.add(Implies(pair_neighbor[e], data["marked_pairs"][e]))
                triple_count = Sum([If(q, 1, 0) for q in triple_neighbor.values()])
                all_neighbors = list(triple_neighbor.values()) + list(pair_neighbor.values())
                solver.add(Sum([If(q, 1, 0) for q in all_neighbors]) == 5)
                misses = []
                for missing_color in range(3):
                    group = [pair_neighbor[e] for e in pairs
                             if missing_color not in {outer.color(e[0]), outer.color(e[1])}]
                    hit = Sum([If(q, 1, 0) for q in group])
                    solver.add(hit <= 1)
                    misses.append(If(hit == 0, 1, 0))
                solver.add(Sum(misses) == triple_count - 2)
                neighbor_point = {}
                for b in range(outer.N):
                    uses = ([triple_neighbor[t] for t in triples if b in t]
                            + [pair_neighbor[e] for e in pairs if b in e])
                    solver.add(Sum([If(q, 1, 0) for q in uses]) <= 1)
                    neighbor_point[b] = Or(uses)
                anchor_point = {
                    b: Or([anchor[t] for t in triples if b in t])
                    for b in range(outer.N)
                }
                for a in range(outer.N):
                    for b in range(a + 1, outer.N):
                        solver.add(Implies(data["k"][outer.edge_key(a, b)],
                                           Not(Or(And(anchor_point[a], neighbor_point[b]),
                                                  And(anchor_point[b], neighbor_point[a])))))
            for t in triples:
                solver.add(Sum([If(anchor[t], 1, 0) for anchor in class_anchors]) ==
                           If(data["classes"][class_index][t], 1, 0))
    return solver, data


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--branch", type=int, choices=(3, 4), required=True)
    parser.add_argument("--timeout-seconds", type=int, default=300)
    parser.add_argument("--all-holes", action="store_true")
    parser.add_argument("--diagonal-rows", action="store_true")
    parser.add_argument("--all-regular-classes", action="store_true")
    args = parser.parse_args()
    solver, _ = build(args.branch, args.timeout_seconds * 1000, args.all_holes,
                      args.diagonal_rows, args.all_regular_classes)
    started = time.time()
    result = solver.check()
    elapsed = time.time() - started
    print(f"branch={args.branch} result={result} elapsed={elapsed:.3f}s")
    if result == unknown:
        print(f"reason_unknown={solver.reason_unknown()}")
        return 2
    if result == sat:
        print("requested exceptional-hole six-pack system exists")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
