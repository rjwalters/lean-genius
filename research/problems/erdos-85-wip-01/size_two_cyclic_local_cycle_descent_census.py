#!/usr/bin/env python3
"""Enumerate local column-cycle descent in a two-hole routing block."""

from __future__ import annotations

import argparse
from itertools import combinations, permutations


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("q", type=int, nargs="?", default=8)
    parser.add_argument("--a", type=int, action="append",
                        help="hole representative; repeat to select several")
    args = parser.parse_args()
    q = args.q
    residues = tuple(r for r in range(q) if r not in {0, 1})
    parameters = args.a if args.a is not None else list(range(q // 2))

    def colors(t: int, values: tuple[int, ...] | list[int]) -> list[int]:
        return [(-t - r - s) % q for r, s in zip(residues, values)]

    for raw_a in parameters:
        a = raw_a % q
        differences = set(range(q)) - {a, (-1 - a) % q}
        print(f"a={a} differences={sorted(differences)}")
        for t in sorted(differences):
            def valid(values: tuple[int, ...] | list[int]) -> bool:
                targets = colors(t, values)
                return (all(u in differences for u in targets) and
                        not any((t + r) % q == 0 and u == t
                                for r, u in zip(residues, targets)))

            def rank(values: tuple[int, ...] | list[int]) -> int:
                return len(differences - set(colors(t, values)))

            def parity(values: tuple[int, ...] | list[int]) -> int:
                return sum(values[i] > values[j]
                           for i in range(len(values))
                           for j in range(i + 1, len(values))) % 2

            local = [(values, rank(values)) for values in permutations(residues)
                     if valid(values)]
            minimum = min(value for _, value in local)
            nonminimum = need_three = stuck = same_parity_stuck = 0
            max_same_parity_support = 0
            for values, old_rank in local:
                if old_rank <= minimum:
                    continue
                nonminimum += 1
                same_parity_supports = [
                    sum(left != right for left, right in zip(values, target))
                    for target, target_rank in local
                    if target_rank < old_rank and parity(target) == parity(values)
                ]
                if same_parity_supports:
                    max_same_parity_support = max(
                        max_same_parity_support, min(same_parity_supports))
                else:
                    same_parity_stuck += 1
                descends = False
                for i, j in combinations(range(len(residues)), 2):
                    changed = list(values)
                    changed[i], changed[j] = changed[j], changed[i]
                    if valid(changed) and rank(changed) < old_rank:
                        descends = True
                        break
                if descends:
                    continue
                need_three += 1
                for i, j, k in combinations(range(len(residues)), 3):
                    for cycle in ((j, k, i), (k, i, j)):
                        changed = list(values)
                        changed[i], changed[j], changed[k] = (
                            values[cycle[0]], values[cycle[1]], values[cycle[2]])
                        if valid(changed) and rank(changed) < old_rank:
                            descends = True
                            break
                    if descends:
                        break
                if not descends:
                    stuck += 1
            print(f"  t={t} minimum={minimum} nonminimum={nonminimum} "
                  f"need_three={need_three} stuck_after_three={stuck} "
                  f"same_parity_stuck={same_parity_stuck} "
                  f"max_same_parity_support={max_same_parity_support}")


if __name__ == "__main__":
    main()
