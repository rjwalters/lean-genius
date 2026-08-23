#!/usr/bin/env python3
"""Stage the two branch-3 non-diagonal regular-class exact partitions.

First generate an outer design that admits all exact row packs for one of
the two regular triple classes, together with both exceptional packs, hole
reciprocity, and the full-pack overlap cap.  Freeze the complete outer
``Q,K`` data, then ask whether the other regular class extends on that same
outer.  This separates a true cross-class incompatibility signal from the
rarity of one-class-extendible outer designs.

Exploratory only: an UNSAT result still needs an independently checked
certificate or a kernel proof.
"""

from __future__ import annotations

import argparse
import time

from z3 import Not, is_true, sat, unknown

from q9_exceptional_hole_sixpack_sat import build
from q9_three_high_u1_design_sat import color


OUTER_MAPS = ("holes", "marked_pairs", "selected", "k")


def chosen(mapping: dict, model) -> list[tuple[int, ...]]:
    return sorted(
        key for key, variable in mapping.items()
        if is_true(model.eval(variable, model_completion=True))
    )


def regular_row_pack_profile(anchor: tuple[int, ...], triples, pairs,
                             k_edges: set[tuple[int, int]]) -> dict:
    """Measure the independent five-neighbor deficit of one regular row."""
    def core_compatible(block) -> bool:
        return all(
            tuple(sorted((a, b))) not in k_edges
            for a in anchor for b in block if a != b
        )

    candidates = [
        (block, None) for block in triples
        if block != anchor and core_compatible(block)
    ] + [
        (block, next(c for c in range(3)
                     if c not in {color(block[0]), color(block[1])}))
        for block in pairs if core_compatible(block)
    ]

    def maximum(enforce_pair_supports: bool) -> int:
        best = 0

        def search(start: int, used_points: set[int],
                   pair_supports: set[int], count: int) -> None:
            nonlocal best
            best = max(best, count)
            if count == 5 or len(candidates) - start <= best - count:
                return
            for index in range(start, len(candidates)):
                block, support = candidates[index]
                if used_points.intersection(block):
                    continue
                if (enforce_pair_supports and support is not None
                        and support in pair_supports):
                    continue
                search(
                    index + 1, used_points.union(block),
                    pair_supports | (
                        {support} if support is not None else set()
                    ), count + 1,
                )

        search(0, set(), set(), 0)
        return best

    typed_maximum = maximum(True)
    return {
        "candidate_count": len(candidates),
        "disjoint_maximum": maximum(False),
        "typed_maximum": typed_maximum,
        "exact_pack": typed_maximum >= 5,
    }


def regular_row_pack_exists(anchor: tuple[int, ...], triples, pairs,
                            k_edges: set[tuple[int, int]]) -> bool:
    """Check exactly the independent five-neighbor constraints for one row."""
    return regular_row_pack_profile(anchor, triples, pairs, k_edges)[
        "exact_pack"
    ]


def print_target_local_feasibility(source_data: dict, model,
                                   target_class: int) -> None:
    triples = chosen(source_data["selected"], model)
    pairs = chosen(source_data["marked_pairs"], model)
    k_edges = set(chosen(source_data["k"], model))
    anchors = chosen(source_data["classes"][target_class], model)
    statuses = [
        [list(anchor), regular_row_pack_profile(
            anchor, triples, pairs, k_edges)]
        for anchor in anchors
    ]
    print(f"target_class={target_class}_local_rows={statuses}", flush=True)


def freeze_outer(source_data: dict, source_model, target_solver,
                 target_data: dict) -> None:
    """Fix every outer class/block/core variable to the source model."""
    for key in OUTER_MAPS:
        for index, variable in target_data[key].items():
            value = is_true(source_model.eval(
                source_data[key][index], model_completion=True
            ))
            target_solver.add(variable if value else Not(variable))
    for class_index in range(3):
        for index, variable in target_data["classes"][class_index].items():
            value = is_true(source_model.eval(
                source_data["classes"][class_index][index],
                model_completion=True,
            ))
            target_solver.add(variable if value else Not(variable))


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source-class", type=int, choices=(1, 2), required=True)
    parser.add_argument("--random-seed", type=int, default=0)
    parser.add_argument("--source-timeout-seconds", type=int, default=180)
    parser.add_argument("--extension-timeout-seconds", type=int, default=60)
    args = parser.parse_args()
    target_class = 3 - args.source_class
    common = {
        "hole_reciprocity": True,
        "hole_full_pack_overlap_cap": True,
    }
    source_solver, source_data = build(
        3, args.source_timeout_seconds * 1000, True,
        regular_class_indices=(args.source_class,), **common,
    )
    source_solver.set(random_seed=args.random_seed)
    started = time.time()
    source_result = source_solver.check()
    print(
        f"source_class={args.source_class} result={source_result} "
        f"elapsed={time.time() - started:.3f}s",
        flush=True,
    )
    if source_result == unknown:
        print("source_reason_unknown=" + source_solver.reason_unknown())
        return 2
    if source_result != sat:
        return 1

    source_model = source_solver.model()
    print_target_local_feasibility(source_data, source_model, target_class)
    target_solver, target_data = build(
        3, args.extension_timeout_seconds * 1000, True,
        regular_class_indices=(target_class,), **common,
    )
    freeze_outer(
        source_data, source_model, target_solver, target_data
    )
    started = time.time()
    target_result = target_solver.check()
    print(
        f"fixed_outer_target_class={target_class} result={target_result} "
        f"elapsed={time.time() - started:.3f}s"
    )
    if target_result == unknown:
        print("target_reason_unknown=" + target_solver.reason_unknown())
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
