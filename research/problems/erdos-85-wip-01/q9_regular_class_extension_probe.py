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


OUTER_MAPS = ("holes", "marked_pairs", "selected", "k")


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

    target_solver, target_data = build(
        3, args.extension_timeout_seconds * 1000, True,
        regular_class_indices=(target_class,), **common,
    )
    freeze_outer(
        source_data, source_solver.model(), target_solver, target_data
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
