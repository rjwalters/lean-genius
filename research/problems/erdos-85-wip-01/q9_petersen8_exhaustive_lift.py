#!/usr/bin/env python3
"""Coverage audit and exhaustive Petersen^8 lift suite.

The 324 transitive-action quotient patterns collapse to 19 patterns under
component relabeling.  Twelve are UNSAT without any action assumption.  The
remaining seven split into 39 orbits under the normalizers of their
transitive component groups; every representative is UNSAT with the lifted
action constraints.

Without ``--verify`` this script cheaply proves that the pinned 51-case list
covers all 324 action-pattern pairs.  With ``--verify`` it reruns Kissat on
all representatives in parallel and requires every result to be UNSAT.
"""

from __future__ import annotations

import argparse
import subprocess
from collections import defaultdict
from concurrent.futures import ThreadPoolExecutor, as_completed
from itertools import permutations
from pathlib import Path

from q9_petersen8_quotient_patterns import (
    TRIPLES,
    canonical_component_pattern,
    gap_transitive_generators,
    patterns,
    triple_orbits,
)


BASE_REPRESENTATIVES = (
    (1, 0), (1, 1), (1, 3), (1, 4), (1, 8), (1, 15), (1, 20),
    (2, 1), (2, 2), (5, 3), (5, 4), (5, 8),
)

ACTION_REPRESENTATIVES = {
    1: (5, 9, 10, 11, 16, 17, 21),
    2: (7, 8, 14),
    4: (1, 2),
    5: (42, 46, 47, 54, 86, 87),
    6: (1, 2, 3, 4),
    7: (1, 2),
    8: (5, 9, 10, 11, 16, 17, 21),
    11: (1, 2),
    12: (0, 1),
    15: (1, 2),
    23: (0, 1),
}


def compose(left: tuple[int, ...], right: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(left[right[index]] for index in range(8))


def inverse(permutation: tuple[int, ...]) -> tuple[int, ...]:
    result = [0] * 8
    for source, target in enumerate(permutation):
        result[target] = source
    return tuple(result)


def generated_group(generators: list[tuple[int, ...]]) -> set[tuple[int, ...]]:
    identity = tuple(range(8))
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


def relabeled_vector(multiplicity, relabel):
    image = {
        tuple(sorted(relabel[vertex] for vertex in triple)): value
        for triple, value in multiplicity.items()
    }
    return tuple(image[triple] for triple in TRIPLES)


def audit_coverage():
    groups = gap_transitive_generators()
    records = {}
    for group_index, _, generators in groups:
        orbits = triple_orbits(generators)
        _, surviving = patterns(orbits, generators)
        for pattern_index, weights in enumerate(sorted(surviving)):
            multiplicity = {
                triple: next(
                    weight for orbit, weight in zip(orbits, weights) if triple in orbit
                )
                for triple in TRIPLES
            }
            records[group_index, pattern_index] = (
                multiplicity,
                canonical_component_pattern(multiplicity),
            )
    assert len(records) == 324
    all_geometric = {canonical for _, canonical in records.values()}
    assert len(all_geometric) == 19
    base_geometric = {records[reference][1] for reference in BASE_REPRESENTATIVES}
    assert len(base_geometric) == 12
    hard_geometric = all_geometric - base_geometric
    assert len(hard_geometric) == 7

    expected_action_representatives = {}
    for group_index, group_order, generators in groups:
        hard_patterns = {
            pattern_index: multiplicity
            for (index, pattern_index), (multiplicity, canonical) in records.items()
            if index == group_index and canonical in hard_geometric
        }
        if not hard_patterns:
            continue
        group = generated_group(generators)
        assert len(group) == group_order
        normalizer = []
        for relabel in permutations(range(8)):
            relabel_inverse = inverse(relabel)
            if all(
                compose(compose(relabel, generator), relabel_inverse) in group
                for generator in generators
            ):
                normalizer.append(relabel)
        classes = defaultdict(list)
        for pattern_index, multiplicity in hard_patterns.items():
            canonical = min(
                relabeled_vector(multiplicity, relabel) for relabel in normalizer
            )
            classes[canonical].append(pattern_index)
        expected_action_representatives[group_index] = tuple(
            sorted(min(patterns_in_class) for patterns_in_class in classes.values())
        )
    assert expected_action_representatives == ACTION_REPRESENTATIVES
    assert sum(map(len, ACTION_REPRESENTATIVES.values())) == 39
    return records


def run_case(script: Path, group: int, pattern: int, without_action: bool) -> str:
    command = [
        "python3", str(script), "--group", str(group), "--pattern", str(pattern),
        "--max-rounds", "0", "--time-seconds",
        "300" if (group, pattern) in {(1, 4), (5, 54), (5, 87)} else "60",
        "--seed", "1",
    ]
    if without_action:
        command.append("--without-action")
    process = subprocess.run(command, text=True, capture_output=True, check=True)
    output = process.stdout.strip()
    if " result=unsat " not in f" {output} ":
        raise RuntimeError(output)
    return output


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--verify", action="store_true")
    parser.add_argument("--workers", type=int, default=4)
    args = parser.parse_args()
    audit_coverage()
    print("coverage action_patterns=324 geometric_patterns=19 base_unsat=12 action_classes=39")
    if not args.verify:
        return
    script = Path(__file__).with_name("q9_petersen8_kissat_lift.py")
    cases = [(group, pattern, True) for group, pattern in BASE_REPRESENTATIVES]
    cases.extend(
        (group, pattern, False)
        for group, pattern_indices in ACTION_REPRESENTATIVES.items()
        for pattern in pattern_indices
    )
    with ThreadPoolExecutor(max_workers=args.workers) as executor:
        futures = {
            executor.submit(run_case, script, *case): case for case in cases
        }
        for future in as_completed(futures):
            print(future.result(), flush=True)
    print("excluded_petersen8_action_patterns 324")


if __name__ == "__main__":
    main()
