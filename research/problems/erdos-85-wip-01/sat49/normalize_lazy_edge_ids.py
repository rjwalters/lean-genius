#!/usr/bin/env python3
"""Normalize recovered order-49 SAT artifacts to Lean's edge numbering.

The historical PySAT generators allocated the 1176 named edge variables on
first use through ``IDPool``.  The Lean generator instead gives ``{i,j}`` its
one-based position in the global lexicographic list of unordered pairs.  This
script reconstructs the historical allocation order for a supplied high count
and applies the resulting permutation to a DIMACS CNF or textual DRAT proof.

Sequential-counter variables are numbered above 1176 in both encodings and
are left unchanged.  Literal signs, clause order, comments, and headers are
preserved.
"""

from __future__ import annotations

import argparse
import itertools
from pathlib import Path
from typing import Iterator

ORDER = 49
EDGE_VARIABLES = ORDER * (ORDER - 1) // 2


def edge_pair(i: int, j: int) -> tuple[int, int]:
    if not 0 <= i < ORDER or not 0 <= j < ORDER or i == j:
        raise ValueError(f"not a loopless order-{ORDER} edge: {(i, j)}")
    return (i, j) if i < j else (j, i)


def lean_edge_id(i: int, j: int) -> int:
    """Lean's one-based global lexicographic unordered-edge identifier."""
    pair = edge_pair(i, j)
    # There are ORDER-a-1 pairs starting at each first endpoint a.
    a, b = pair
    return a * (2 * ORDER - a - 1) // 2 + (b - a)


def lazy_edge_pairs(high_count: int) -> list[tuple[int, int]]:
    """Reconstruct named-edge first-use order in the recovered generators."""
    if not 0 <= high_count <= ORDER:
        raise ValueError(f"high_count must lie in 0..{ORDER}")

    pairs: list[tuple[int, int]] = []
    seen: set[tuple[int, int]] = set()

    def use(i: int, j: int) -> None:
        pair = edge_pair(i, j)
        if pair not in seen:
            seen.add(pair)
            pairs.append(pair)

    # Fixed high-high and low-high unit prefixes.
    for a, b in itertools.combinations(range(high_count), 2):
        use(a, b)
    for low in range(high_count, ORDER):
        for high in range(high_count):
            use(low, high)

    # Universal C4 segment.  Each emitted clause calls edge(i,w), edge(j,w),
    # edge(i,w2), edge(j,w2) in this order.
    for i, j in itertools.combinations(range(ORDER), 2):
        others = [w for w in range(ORDER) if w != i and w != j]
        for w, w2 in itertools.combinations(others, 2):
            use(i, w)
            use(j, w)
            use(i, w2)
            use(j, w2)

    if len(pairs) != EDGE_VARIABLES:
        raise AssertionError(
            f"allocation recovered {len(pairs)} edges, expected {EDGE_VARIABLES}"
        )
    return pairs


def lazy_to_lean_permutation(high_count: int) -> list[int]:
    """Index ``old_id`` to its Lean id; index zero is an unused sentinel."""
    permutation = [0]
    permutation.extend(lean_edge_id(*pair) for pair in lazy_edge_pairs(high_count))
    if sorted(permutation[1:]) != list(range(1, EDGE_VARIABLES + 1)):
        raise AssertionError("edge-id map is not a permutation")
    return permutation


def recover_permutation_from_c4_segment(
    source: Path, prefix_clauses: int
) -> list[int]:
    """Recover arbitrary historical edge allocation from its universal C4 block.

    Some scout generators emitted geometry-specific edge units before the
    fixed support prefix, so their ``IDPool`` order is not determined by the
    high count alone.  The following universal C4 block names every edge and
    has a fixed clause order, allowing its old ids to be matched directly to
    Lean's lexicographic ids.
    """
    actual = itertools.islice(dimacs_clauses(source), prefix_clauses, None)
    permutation = [0] * (EDGE_VARIABLES + 1)
    clause_count = 0
    for i, j in itertools.combinations(range(ORDER), 2):
        others = [w for w in range(ORDER) if w != i and w != j]
        for w, w2 in itertools.combinations(others, 2):
            try:
                clause = next(actual)
            except StopIteration as error:
                raise ValueError("source ended inside the universal C4 block") from error
            expected = ((i, w), (j, w), (i, w2), (j, w2))
            if len(clause) != 4 or any(literal >= 0 for literal in clause):
                raise ValueError(
                    f"clause {prefix_clauses + clause_count + 1} is not a C4 clause"
                )
            for literal, pair in zip(clause, expected):
                old_id = abs(literal)
                if old_id > EDGE_VARIABLES:
                    raise ValueError("auxiliary variable appeared in the C4 block")
                new_id = lean_edge_id(*pair)
                if permutation[old_id] not in (0, new_id):
                    raise ValueError(
                        f"inconsistent edge id {old_id}: "
                        f"{permutation[old_id]} versus {new_id}"
                    )
                permutation[old_id] = new_id
            clause_count += 1
    if 0 in permutation[1:]:
        missing = [index for index, value in enumerate(permutation) if index and not value]
        raise ValueError(f"C4 block did not expose edge ids: {missing[:10]}")
    if sorted(permutation[1:]) != list(range(1, EDGE_VARIABLES + 1)):
        raise ValueError("recovered edge-id map is not a permutation")
    return permutation


def permute_literal(literal: int, permutation: list[int]) -> int:
    variable = abs(literal)
    if variable == 0 or variable > EDGE_VARIABLES:
        return literal
    normalized = permutation[variable]
    return normalized if literal > 0 else -normalized


def normalize_line(line: str, permutation: list[int]) -> str:
    stripped = line.strip()
    if not stripped or stripped.startswith(("c", "p")):
        return line
    fields = stripped.split()
    deletion = fields[0] == "d"
    start = 1 if deletion else 0
    output = fields[:start]
    for field in fields[start:]:
        literal = int(field)
        output.append(str(permute_literal(literal, permutation)))
    return " ".join(output) + "\n"


def normalize_file(
    source: Path, target: Path, high_count: int,
    recover_c4_prefix: int | None = None,
) -> None:
    if source.resolve() == target.resolve():
        raise ValueError("source and target must be different paths")
    permutation = (
        recover_permutation_from_c4_segment(source, recover_c4_prefix)
        if recover_c4_prefix is not None
        else lazy_to_lean_permutation(high_count)
    )
    target.parent.mkdir(parents=True, exist_ok=True)
    with source.open() as incoming, target.open("w") as outgoing:
        for line in incoming:
            outgoing.write(normalize_line(line, permutation))


def dimacs_clauses(path: Path) -> Iterator[list[int]]:
    with path.open() as stream:
        for line in stream:
            stripped = line.strip()
            if not stripped or stripped.startswith(("c", "p")):
                continue
            clause = [int(field) for field in stripped.split()]
            if not clause or clause[-1] != 0:
                raise ValueError(f"unterminated DIMACS clause in {path}: {stripped}")
            yield clause[:-1]


def decoded_fixed_masks(path: Path, high_count: int) -> list[int]:
    fixed_count = high_count * (high_count - 1) // 2 + (ORDER - high_count) * high_count
    units = list(itertools.islice(dimacs_clauses(path), fixed_count))
    if len(units) != fixed_count or any(len(clause) != 1 for clause in units):
        raise ValueError("fixed prefix is not the expected sequence of unit clauses")
    offset = high_count * (high_count - 1) // 2
    masks = [0] * high_count
    for low in range(high_count, ORDER):
        row = units[offset + (low - high_count) * high_count :
                    offset + (low - high_count + 1) * high_count]
        masks.append(sum(1 << high for high, clause in enumerate(row) if clause[0] > 0))
    return masks


def expected_h5_clauses(masks: list[int]) -> Iterator[list[int]]:
    """The exact four Lean segments, generated independently in Python."""
    from pysat.card import CardEnc, EncType

    high_count = 5
    if len(masks) != ORDER or any(masks[high] != 0 for high in range(high_count)):
        raise ValueError("h5 verification expects 49 masks with a zero high prefix")

    for a, b in itertools.combinations(range(high_count), 2):
        yield [-lean_edge_id(a, b)]
    for low in range(high_count, ORDER):
        for high in range(high_count):
            literal = lean_edge_id(low, high)
            yield [literal if masks[low] & (1 << high) else -literal]

    for i, j in itertools.combinations(range(ORDER), 2):
        others = [w for w in range(ORDER) if w != i and w != j]
        for w, w2 in itertools.combinations(others, 2):
            yield [
                -lean_edge_id(i, w), -lean_edge_id(j, w),
                -lean_edge_id(i, w2), -lean_edge_id(j, w2),
            ]

    top = EDGE_VARIABLES
    for vertex in range(ORDER):
        incident = [lean_edge_id(vertex, other) for other in range(ORDER)
                    if other != vertex]
        block = CardEnc.equals(
            lits=incident,
            bound=8 if vertex < high_count else 7,
            top_id=top,
            encoding=EncType.seqcounter,
        )
        top = block.nv
        yield from block.clauses

    neighborhoods = {
        high: [low for low in range(high_count, ORDER)
               if masks[low] & (1 << high)]
        for high in range(high_count)
    }
    for low in range(high_count, ORDER):
        for high in range(high_count):
            yield [lean_edge_id(low, member)
                   for member in neighborhoods[high] if member != low]


def verify_normalized_h5(source: Path, normalized: Path) -> int:
    masks = decoded_fixed_masks(source, 5)
    actual = dimacs_clauses(normalized)
    expected = expected_h5_clauses(masks)
    count = 0
    for count, pair in enumerate(itertools.zip_longest(actual, expected), start=1):
        got, wanted = pair
        if got != wanted:
            raise AssertionError(
                f"normalized h5 mismatch at clause {count}: got {got}, expected {wanted}"
            )
    return count


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--high-count", type=int, required=True)
    parser.add_argument(
        "--verify-h5", action="store_true",
        help="independently regenerate and compare the exact four h5 segments",
    )
    parser.add_argument(
        "--recover-c4-prefix", type=int,
        help=("recover an arbitrary lazy edge allocation from the universal C4 "
              "block beginning after this many clauses"),
    )
    parser.add_argument("source", type=Path)
    parser.add_argument("target", type=Path)
    args = parser.parse_args()
    normalize_file(args.source, args.target, args.high_count, args.recover_c4_prefix)
    if args.verify_h5:
        if args.high_count != 5:
            parser.error("--verify-h5 requires --high-count 5")
        count = verify_normalized_h5(args.source, args.target)
        print(f"verified {count} normalized h5 clauses")


if __name__ == "__main__":
    main()
