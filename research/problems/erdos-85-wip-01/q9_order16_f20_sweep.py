#!/usr/bin/env python3
"""Exhaust the symmetry-reduced F20 lifts of the order-16x5 q=9 shadow.

For a fixed closing twist ``alpha``, its centralizer in ``Aut(C)`` acts on
the possible equal-pattern fibers and their bijections with the local F20
pattern orbit.  This driver computes those orbits rather than relying on a
hand-written branch list, then requires every representative formula to be
proved UNSAT by ``q9_order16_endpoint_lift_sat.py``.
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor, as_completed
from itertools import permutations
from pathlib import Path

import networkx as nx

from q9_order16_endpoint_lift_sat import (
    EXPECTED_SHA256,
    FIBER_PARTITIONS_4,
    FIBER_PARTITIONS_8,
    component_ordinal_4,
)

import hashlib


def compose(left: tuple[int, ...], right: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(left[right[vertex]] for vertex in range(16))


def inverse(permutation: tuple[int, ...]) -> tuple[int, ...]:
    result = [0] * 16
    for vertex, image in enumerate(permutation):
        result[image] = vertex
    return tuple(result)


def automorphism_data(component: nx.Graph):
    automorphisms = sorted(
        tuple(mapping[vertex] for vertex in range(16))
        for mapping in nx.algorithms.isomorphism.GraphMatcher(
            component, component
        ).isomorphisms_iter()
    )
    assert len(automorphisms) == 96
    unseen = set(automorphisms)
    classes = []
    while unseen:
        representative = min(unseen)
        conjugacy_class = {
            compose(compose(group_element, representative), inverse(group_element))
            for group_element in automorphisms
        }
        unseen -= conjugacy_class
        classes.append((representative, len(conjugacy_class)))
    classes.sort()
    assert [size for _, size in classes] == [1, 8, 12, 12, 8, 8, 2, 6, 8, 12, 12, 6, 1]
    return automorphisms, classes


def assignment_representatives(
    partitions: tuple[tuple[tuple[int, ...], ...], ...],
    centralizer: list[tuple[int, ...]],
) -> list[tuple[int, int]]:
    """Return centralizer-orbit representatives as (partition, bijection)."""
    assignment_to_branch = {}
    for partition_index, partition in enumerate(partitions):
        for bijection_index, bijection in enumerate(permutations(range(len(partition)))):
            assignment = [None] * 16
            for fiber_index, fiber in enumerate(partition):
                for point in fiber:
                    assignment[point] = bijection[fiber_index]
            assignment = tuple(assignment)
            assert assignment not in assignment_to_branch
            assignment_to_branch[assignment] = (partition_index, bijection_index)

    unseen = set(assignment_to_branch)
    representatives = []
    while unseen:
        seed = min(unseen)
        orbit = {
            tuple(seed[inverse(group_element)[point]] for point in range(16))
            for group_element in centralizer
        }
        # The partition catalogs are closed under the full automorphism group.
        assert orbit <= assignment_to_branch.keys()
        unseen -= orbit
        representative = min(orbit)
        representatives.append(assignment_to_branch[representative])
    return sorted(representatives)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("census", type=Path)
    parser.add_argument("--rotation-class", type=int)
    parser.add_argument("--f20-pattern", type=int)
    parser.add_argument("--jobs", type=int, default=1)
    parser.add_argument("--max-rounds", type=int, default=0)
    parser.add_argument("--kissat-seed", type=int, default=0)
    parser.add_argument("--checkpoint", type=Path)
    parser.add_argument("--list", action="store_true")
    args = parser.parse_args()

    raw = args.census.read_bytes()
    assert hashlib.sha256(raw).hexdigest() == EXPECTED_SHA256
    component = component_ordinal_4(raw)
    automorphisms, rotation_classes = automorphism_data(component)
    class_indices = (
        [args.rotation_class]
        if args.rotation_class is not None
        else list(range(len(rotation_classes)))
    )
    pattern_indices = (
        [args.f20_pattern]
        if args.f20_pattern is not None
        else list(range(6))
    )

    branches = []
    coverage = []
    for class_index in class_indices:
        alpha, _ = rotation_classes[class_index]
        centralizer = [
            beta
            for beta in automorphisms
            if compose(beta, alpha) == compose(alpha, beta)
        ]
        for pattern_index in pattern_indices:
            partitions = FIBER_PARTITIONS_8 if pattern_index < 2 else FIBER_PARTITIONS_4
            representatives = assignment_representatives(partitions, centralizer)
            coverage.append((class_index, pattern_index, len(centralizer), len(representatives)))
            branches.extend(
                (class_index, pattern_index, partition_index, bijection_index)
                for partition_index, bijection_index in representatives
            )

    for item in coverage:
        print(
            f"coverage rotation_class={item[0]} pattern={item[1]} "
            f"centralizer_order={item[2]} representatives={item[3]}"
        )
    print(f"total_representatives={len(branches)}", flush=True)
    if args.list:
        for branch in branches:
            print("branch", *branch)
        return

    verifier = Path(__file__).with_name("q9_order16_endpoint_lift_sat.py")
    completed_branches = set()
    if args.checkpoint is not None and args.checkpoint.exists():
        completed_branches = {
            tuple(branch) for branch in json.loads(args.checkpoint.read_text())["completed"]
        }
        assert completed_branches <= set(branches)
        print(f"resumed_completed={len(completed_branches)}", flush=True)
    pending_branches = [branch for branch in branches if branch not in completed_branches]

    def save_checkpoint() -> None:
        if args.checkpoint is None:
            return
        temporary = args.checkpoint.with_suffix(args.checkpoint.suffix + ".tmp")
        temporary.write_text(
            json.dumps(
                {
                    "completed": [list(branch) for branch in sorted(completed_branches)],
                    "expected": len(branches),
                },
                indent=2,
            )
            + "\n"
        )
        os.replace(temporary, args.checkpoint)

    def check(branch: tuple[int, int, int, int]):
        class_index, pattern_index, partition_index, bijection_index = branch
        command = [
            sys.executable,
            str(verifier),
            str(args.census),
            "--quotient", "uniform",
            "--stabilizer", "f20",
            "--rotation-class", str(class_index),
            "--f20-pattern", str(pattern_index),
            "--fiber-partition", str(partition_index),
            "--fiber-bijection", str(bijection_index),
            "--encoding", "lazy",
            "--max-rounds", str(args.max_rounds),
            "--kissat-mode", "unsat",
            "--kissat-seed", str(args.kissat_seed),
        ]
        process = subprocess.run(command, text=True, capture_output=True)
        if process.returncode != 0 or "UNSAT backend=kissat" not in process.stdout:
            raise RuntimeError(
                f"branch={branch} status={process.returncode}\n"
                f"stdout:\n{process.stdout}\nstderr:\n{process.stderr}"
            )
        return branch

    completed = len(completed_branches)
    with ThreadPoolExecutor(max_workers=args.jobs) as executor:
        futures = {
            executor.submit(check, branch): branch for branch in pending_branches
        }
        for future in as_completed(futures):
            branch = future.result()
            completed += 1
            completed_branches.add(branch)
            save_checkpoint()
            print(f"completed branch={branch} count={completed}/{len(branches)}", flush=True)
    assert completed == len(branches)
    print(
        f"UNSAT f20_representatives={completed} "
        f"rotation_classes={len(class_indices)} patterns={len(pattern_indices)}"
    )
    print("excluded_uniform_action=F20")


if __name__ == "__main__":
    main()
