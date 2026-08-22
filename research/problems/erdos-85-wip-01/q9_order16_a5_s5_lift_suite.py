#!/usr/bin/env python3
"""Independent coverage audit and A5/S5 order-16x5 lift suite.

The component stabilizer acts on the other four blocks as A4 (or S4).  Its
equivariant three-line pattern at a point must have orbit size dividing 16;
the only possibilities are the four stars and four complementary triangles.
This script independently reconstructs that orbit calculation, the 19
four-by-four imprimitivity systems in the component, and the 13 closing-twist
classes.  The SAT formulas deliberately use the weaker condition that every
point is some star/triangle, so UNSAT covers every fiber partition at once.
"""

from __future__ import annotations

import argparse
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor, as_completed
from itertools import combinations, combinations_with_replacement, permutations
from pathlib import Path

import networkx as nx

from q9_order16_endpoint_lift_sat import (
    FIBER_PARTITIONS_4,
    component_ordinal_4,
)
ROTATION_CLASS_SIZES = (1, 8, 12, 12, 8, 8, 2, 6, 8, 12, 12, 6, 1)


def compose(left, right):
    return tuple(left[right[index]] for index in range(len(left)))


def inverse(permutation):
    result = [0] * len(permutation)
    for source, target in enumerate(permutation):
        result[target] = source
    return tuple(result)


def generated_group(generators, degree):
    identity = tuple(range(degree))
    group = {identity}
    frontier = [identity]
    while frontier:
        element = frontier.pop()
        for generator in generators:
            image = compose(generator, element)
            if image not in group:
                group.add(image)
                frontier.append(image)
    return group


def cycle_notation(permutation):
    unseen = set(range(len(permutation)))
    cycles = []
    while unseen:
        start = min(unseen)
        if permutation[start] == start:
            unseen.remove(start)
            continue
        cycle = []
        vertex = start
        while vertex in unseen:
            unseen.remove(vertex)
            cycle.append(vertex + 1)
            vertex = permutation[vertex]
        cycles.append("(" + ",".join(map(str, cycle)) + ")")
    return "".join(cycles) or "()"


def gap_transitive_representatives(generators, degree):
    encoded = ",".join(cycle_notation(generator) for generator in generators)
    gap_code = f"""
SizeScreen([100000,100000]);;
G:=Group([{encoded}]);;
classes:=ConjugacyClassesSubgroups(G);;
trans:=Filtered(classes,c->IsTransitive(Representative(c),[1..{degree}]));;
Print("META|",Size(G),"|",Length(classes),"|",Length(trans),"\\n");;
for c in trans do
  H:=Representative(c);;
  Print("H|",Size(H),"|",Size(c),"|");;
  first:=true;;
  for gen in GeneratorsOfGroup(H) do
    if not first then Print(";"); fi;; first:=false;;
    Print(JoinStringsWithSeparator(List([1..{degree}],i->String(i^gen)),","));;
  od;; Print("\\n");;
od;; QUIT;
"""
    process = subprocess.run(
        ["docker", "run", "--rm", "-i", "gapsystem/gap-docker", "gap", "-q"],
        input=gap_code, text=True, capture_output=True, check=True,
    )
    lines = [line.strip() for line in process.stdout.splitlines() if line.strip()]
    tag, order, class_count, transitive_count = lines[0].split("|")
    assert tag == "META"
    representatives = []
    for line in lines[1:]:
        tag, subgroup_order, class_size, encoded_generators = line.split("|")
        assert tag == "H"
        subgroup_generators = [
            tuple(int(image) - 1 for image in generator.split(","))
            for generator in encoded_generators.split(";")
        ]
        representatives.append(
            (int(subgroup_order), int(class_size), subgroup_generators)
        )
    assert len(representatives) == int(transitive_count)
    return (int(order), int(class_count), int(transitive_count)), representatives


def audit_patterns() -> None:
    vertices = range(4)
    pairs = list(combinations(vertices, 2))
    even = [
        permutation
        for permutation in permutations(vertices)
        if sum(
            permutation[left] > permutation[right]
            for left, right in combinations(vertices, 2)
        ) % 2 == 0
    ]
    actions = [
        tuple(
            pairs.index(tuple(sorted((permutation[left], permutation[right]))))
            for left, right in pairs
        )
        for permutation in even
    ]
    unseen = {
        tuple(multiset.count(index) for index in range(6))
        for multiset in combinations_with_replacement(range(6), 3)
    }
    orbits = []
    while unseen:
        pattern = min(unseen)
        orbit = {
            tuple(pattern[action.index(index)] for index in range(6))
            for action in actions
        }
        unseen -= orbit
        orbits.append(orbit)
    assert sorted(map(len, orbits)) == [4, 4, 6, 6, 6, 6, 12, 12]
    liftable = {frozenset(orbit) for orbit in orbits if 16 % len(orbit) == 0}
    stars = frozenset(
        tuple(int(distinguished in pair) for pair in pairs)
        for distinguished in vertices
    )
    triangles = frozenset(
        tuple(int(distinguished not in pair) for pair in pairs)
        for distinguished in vertices
    )
    assert liftable == {stars, triangles}


def audit_component(census: Path):
    component = component_ordinal_4(census.read_bytes())
    automorphisms = sorted(
        tuple(mapping[vertex] for vertex in range(16))
        for mapping in nx.algorithms.isomorphism.GraphMatcher(
            component, component
        ).isomorphisms_iter()
    )
    assert len(automorphisms) == 96
    unseen = set(automorphisms)
    class_sizes = []
    while unseen:
        representative = min(unseen)
        conjugates = {
            compose(compose(element, representative), inverse(element))
            for element in automorphisms
        }
        unseen -= conjugates
        class_sizes.append(len(conjugates))
    assert tuple(class_sizes) == ROTATION_CLASS_SIZES

    meta, representatives = gap_transitive_representatives(
        [list(element) for element in automorphisms], degree=16
    )
    assert meta == (96, 42, 8)
    representative_partitions = set()
    for subgroup_order, _, subgroup_generators in representatives:
        subgroup = generated_group(
            [list(generator) for generator in subgroup_generators], 16
        )
        assert len(subgroup) == subgroup_order
        for rest in combinations(range(1, 16), 3):
            block = frozenset((0, *rest))
            images = {frozenset(element[x] for x in block) for element in subgroup}
            if (
                len(images) == 4
                and len(set().union(*images)) == 16
                and all(
                    left == right or left.isdisjoint(right)
                    for left in images for right in images
                )
            ):
                representative_partitions.add(
                    tuple(sorted(tuple(sorted(image)) for image in images))
                )
    partitions = {
        tuple(
            sorted(
                tuple(sorted(element[point] for point in block))
                for block in partition
            )
        )
        for partition in representative_partitions
        for element in automorphisms
    }
    assert len(representative_partitions) == 11
    assert partitions == set(FIBER_PARTITIONS_4)
    return len(representative_partitions), len(partitions)


def cases():
    for stabilizer in ("a5-star", "a5-triangle"):
        for seed_orbit in range(56):
            yield stabilizer, 0, seed_orbit
        for rotation_class in range(1, 13):
            yield stabilizer, rotation_class, None


def run_case(verifier: Path, census: Path, case) -> str:
    stabilizer, rotation_class, seed_orbit = case
    command = [
        sys.executable, str(verifier), str(census),
        "--quotient", "uniform",
        "--stabilizer", stabilizer,
        "--rotation-class", str(rotation_class),
        "--encoding", "direct",
        "--kissat-mode", "unsat",
    ]
    if seed_orbit is not None:
        command.extend(("--seed-orbit", str(seed_orbit)))
    process = subprocess.run(command, text=True, capture_output=True)
    if process.returncode != 0 or "UNSAT backend=kissat rounds=0" not in process.stdout:
        raise RuntimeError(
            f"failed case={case} status={process.returncode}\n"
            f"{process.stdout}{process.stderr}"
        )
    return (
        f"completed stabilizer={stabilizer} rotation_class={rotation_class} "
        f"seed_orbit={seed_orbit}"
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("census", type=Path)
    parser.add_argument("--verify", action="store_true")
    parser.add_argument("--workers", type=int, default=4)
    args = parser.parse_args()
    audit_patterns()
    representative_count, partition_count = audit_component(args.census)
    all_cases = tuple(cases())
    assert len(all_cases) == 136
    print(
        "coverage pattern_orbits=star+triangle",
        f"partition_representatives={representative_count}",
        f"partitions={partition_count}",
        "twist_classes=13",
        f"sat_branches={len(all_cases)}",
        flush=True,
    )
    if not args.verify:
        return
    verifier = Path(__file__).with_name("q9_order16_endpoint_lift_sat.py")
    with ThreadPoolExecutor(max_workers=args.workers) as executor:
        futures = {
            executor.submit(run_case, verifier, args.census, case): case
            for case in all_cases
        }
        for future in as_completed(futures):
            print(future.result(), flush=True)
    print("excluded_uniform_a5_s5_action_patterns 2")


if __name__ == "__main__":
    main()
