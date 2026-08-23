#!/usr/bin/env python3
"""Test the local exceptional-hole six-pack obstruction in the q=9 design.

An exceptional ordinary B0 row is a selected rainbow hole triple.  Its six
residual neighbors must consist of three selected rainbow triples and one
marked-support pair of each missing color.  The two Gram laws proved in Lean
force these six U1 blocks to be pairwise disjoint and every one of them to
have no K-edge to the hole triple.  This script asks whether even one such
local configuration can occur in the full outer 24-point design.

The optional row-family flags strengthen this directed relaxation through
all exceptional holes, the normalized diagonal class, the other regular
triple classes, or all 21 pair-center rows.  ``--pair-reciprocity`` adds only
pair-to-pair symmetry.  This separates local row feasibility from the first
genuinely global agreement constraint without restoring the full residual
graph.

``--hole-reciprocity`` couples the exceptional packs themselves: one selected
hole block occurs among the other's residual triple neighbors exactly when
the reverse occurrence holds.  This is the smallest symmetry consequence
linking the two branch-3 complement partitions.

``--hole-pair-reciprocity`` additionally couples every exceptional row to
all 21 marked-pair rows.  It requires ``--all-holes --all-pair-rows``.

``--hole-pair-choice-overlap-cap`` adds the C4-free cross-hole law: two
distinct exceptional rows can select the same marked-pair center in at most
one of the three supports.

``--hole-full-pack-overlap-cap`` applies the stronger C4-free law to the
entire six-row residual packs: two distinct holes share at most one residual
center total, across both triple and pair rows.

Exploratory only: UNSAT still requires an independently checked certificate
or a kernel proof.
"""

from __future__ import annotations

import argparse
from itertools import combinations
import time
from pathlib import Path
import sys

from z3 import And, Bool, If, Implies, Not, Or, Sum, is_true, sat, unknown

sys.path.insert(0, str(Path(__file__).resolve().parent))
import q9_three_high_u1_design_sat as outer


def exactly_one(xs):
    return Sum([If(x, 1, 0) for x in xs]) == 1


def build(branch: int, timeout_ms: int, all_holes: bool,
          diagonal_rows: bool = False, all_regular_classes: bool = False,
          all_pair_rows: bool = False, pair_reciprocity: bool = False,
          hole_reciprocity: bool = False,
          hole_pair_reciprocity: bool = False,
          hole_pair_choice_overlap_cap: bool = False,
          hole_full_pack_overlap_cap: bool = False):
    solver, data = outer.build(branch, timeout_ms)
    triples = data["triples"]
    pairs = list(data["marked_pairs"])
    pack_count = (2 if branch == 3 else 4) if all_holes else 1
    anchors = []
    hole_triple_neighbors = []
    hole_pair_neighbors = []
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
        hole_triple_neighbors.append(triple_neighbor)
        hole_pair_neighbors.append(pair_neighbor)
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
        if hole_reciprocity:
            for r, s in combinations(range(pack_count), 2):
                r_to_s = Or([
                    And(anchors[s][t], hole_triple_neighbors[r][t])
                    for t in triples
                ])
                s_to_r = Or([
                    And(anchors[r][t], hole_triple_neighbors[s][t])
                    for t in triples
                ])
                solver.add(r_to_s == s_to_r)
    elif hole_reciprocity:
        raise ValueError("hole reciprocity requires all holes")
    if hole_pair_choice_overlap_cap:
        if not all_holes:
            raise ValueError("hole pair-choice overlap cap requires all holes")
        for r, s in combinations(range(pack_count), 2):
            solver.add(Sum([
                If(And(hole_pair_neighbors[r][e],
                       hole_pair_neighbors[s][e]), 1, 0)
                for e in pairs
            ]) <= 1)
    if hole_full_pack_overlap_cap:
        if not all_holes:
            raise ValueError("hole full-pack overlap cap requires all holes")
        for r, s in combinations(range(pack_count), 2):
            solver.add(Sum(
                [If(And(hole_triple_neighbors[r][t],
                        hole_triple_neighbors[s][t]), 1, 0)
                 for t in triples]
                + [If(And(hole_pair_neighbors[r][e],
                          hole_pair_neighbors[s][e]), 1, 0)
                   for e in pairs]
            ) <= 1)
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
    if all_pair_rows:
        pair_miss_matrix = [[[] for _ in range(3)] for _ in range(3)]
        pair_pack_data = [[] for _ in range(3)]
        for anchor_group in range(3):
            group_pairs = [e for e in pairs
                           if anchor_group not in {outer.color(e[0]), outer.color(e[1])}]
            group_anchors = []
            for r in range(7):
                anchor = {
                    e: Bool(f"pairrow_{anchor_group}_{r}_anchor_{e[0]}_{e[1]}")
                    for e in group_pairs
                }
                group_anchors.append(anchor)
                solver.add(exactly_one(anchor.values()))
                triple_neighbor = {
                    t: Bool(f"pairrow_{anchor_group}_{r}_triple_{t[0]}_{t[1]}_{t[2]}")
                    for t in triples
                }
                pair_neighbor = {
                    e: Bool(f"pairrow_{anchor_group}_{r}_pair_{e[0]}_{e[1]}")
                    for e in pairs
                }
                pair_pack_data[anchor_group].append(
                    (anchor, triple_neighbor, pair_neighbor)
                )
                for e in group_pairs:
                    solver.add(Implies(anchor[e], data["marked_pairs"][e]))
                for t in triples:
                    solver.add(Implies(triple_neighbor[t], data["selected"][t]))
                for e in pairs:
                    solver.add(Implies(pair_neighbor[e], data["marked_pairs"][e]))
                    if e in anchor:
                        solver.add(Not(And(anchor[e], pair_neighbor[e])))
                triple_count = Sum([If(q, 1, 0) for q in triple_neighbor.values()])
                all_neighbors = list(triple_neighbor.values()) + list(pair_neighbor.values())
                solver.add(Sum([If(q, 1, 0) for q in all_neighbors]) == 6)
                misses = []
                for missing_color in range(3):
                    support = [pair_neighbor[e] for e in pairs
                               if missing_color not in {outer.color(e[0]), outer.color(e[1])}]
                    hit = Sum([If(q, 1, 0) for q in support])
                    solver.add(hit <= 1)
                    miss = If(hit == 0, 1, 0)
                    misses.append(miss)
                    pair_miss_matrix[anchor_group][missing_color].append(miss)
                solver.add(Sum(misses) == triple_count - 3)
                neighbor_point = {}
                for b in range(outer.N):
                    uses = ([triple_neighbor[t] for t in triples if b in t]
                            + [pair_neighbor[e] for e in pairs if b in e])
                    solver.add(Sum([If(q, 1, 0) for q in uses]) <= 1)
                    neighbor_point[b] = Or(uses)
                anchor_point = {
                    b: Or([anchor[e] for e in group_pairs if b in e])
                    for b in range(outer.N)
                }
                for a in range(outer.N):
                    for b in range(a + 1, outer.N):
                        solver.add(Implies(data["k"][outer.edge_key(a, b)],
                                           Not(Or(And(anchor_point[a], neighbor_point[b]),
                                                  And(anchor_point[b], neighbor_point[a])))))
            for e in group_pairs:
                solver.add(Sum([If(anchor[e], 1, 0) for anchor in group_anchors]) ==
                           If(data["marked_pairs"][e], 1, 0))
        # Symmetry of the residual adjacency forces the pair-group miss
        # matrix to have equal corresponding row and column sums.
        for g in range(3):
            solver.add(Sum(sum(pair_miss_matrix[g], [])) ==
                       Sum(sum([pair_miss_matrix[h][g] for h in range(3)], [])))
        if pair_reciprocity:
            def pair_group(e):
                return next(g for g in range(3)
                            if g not in {outer.color(e[0]), outer.color(e[1])})

            def directed(e, f):
                return Or([And(anchor[e], neighbors[f])
                           for anchor, _, neighbors
                           in pair_pack_data[pair_group(e)]])

            for i, e in enumerate(pairs):
                for f in pairs[i + 1:]:
                    solver.add(directed(e, f) == directed(f, e))
    elif pair_reciprocity:
        raise ValueError("pair reciprocity requires all pair rows")
    if hole_pair_reciprocity:
        if not all_holes or not all_pair_rows:
            raise ValueError(
                "hole-pair reciprocity requires all holes and all pair rows"
            )
        for r in range(pack_count):
            for group_packs in pair_pack_data:
                for pair_anchor, pair_triples, _ in group_packs:
                    hole_to_pair = Or([
                        And(pair_anchor[e], hole_pair_neighbors[r][e])
                        for e in pair_anchor
                    ])
                    pair_to_hole = Or([
                        And(anchors[r][t], pair_triples[t]) for t in triples
                    ])
                    solver.add(hole_to_pair == pair_to_hole)
    data["sixpack_anchors"] = anchors
    data["sixpack_triple_neighbors"] = hole_triple_neighbors
    data["sixpack_pair_neighbors"] = hole_pair_neighbors
    return solver, data


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--branch", type=int, choices=(3, 4), required=True)
    parser.add_argument("--timeout-seconds", type=int, default=300)
    parser.add_argument("--all-holes", action="store_true")
    parser.add_argument("--diagonal-rows", action="store_true")
    parser.add_argument("--all-regular-classes", action="store_true")
    parser.add_argument("--all-pair-rows", action="store_true")
    parser.add_argument("--pair-reciprocity", action="store_true")
    parser.add_argument("--hole-reciprocity", action="store_true")
    parser.add_argument("--hole-pair-reciprocity", action="store_true")
    parser.add_argument(
        "--hole-pair-choice-overlap-cap", action="store_true",
    )
    parser.add_argument(
        "--hole-full-pack-overlap-cap", action="store_true",
    )
    parser.add_argument(
        "--print-hole-packs", action="store_true",
        help="on SAT, print the selected exceptional blocks and six-packs",
    )
    args = parser.parse_args()
    solver, data = build(
        args.branch, args.timeout_seconds * 1000, args.all_holes,
        args.diagonal_rows, args.all_regular_classes,
        args.all_pair_rows, args.pair_reciprocity,
        args.hole_reciprocity, args.hole_pair_reciprocity,
        args.hole_pair_choice_overlap_cap,
        args.hole_full_pack_overlap_cap,
    )
    started = time.time()
    result = solver.check()
    elapsed = time.time() - started
    print(f"branch={args.branch} result={result} elapsed={elapsed:.3f}s")
    if result == unknown:
        print(f"reason_unknown={solver.reason_unknown()}")
        return 2
    if result == sat:
        print("requested exceptional-hole six-pack system exists")
        if args.print_hole_packs:
            model = solver.model()
            for index, (anchor, triples, pairs) in enumerate(zip(
                    data["sixpack_anchors"],
                    data["sixpack_triple_neighbors"],
                    data["sixpack_pair_neighbors"])):
                chosen = lambda mapping: sorted(
                    key for key, value in mapping.items()
                    if is_true(model.eval(value, model_completion=True))
                )
                print(
                    f"pack={index} anchor={chosen(anchor)} "
                    f"triples={chosen(triples)} pairs={chosen(pairs)}"
                )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
