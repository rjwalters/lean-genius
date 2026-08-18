#!/usr/bin/env python3
"""Exact moment ledger for rational square sectors of the order-16 block.

For a 7-regular graph on 16 vertices, the nonprincipal adjacency spectrum
has sum -7 and square-sum 63.  Rational defect eigenvalues for which
``7 - mu`` is a positive integer square are ``mu = 6, 3, -2``, with square
roots 1, 2, 3.  This script enumerates multiplicities compatible with:

* the two spectral moments and Cauchy--Schwarz on the residual spectrum;
* a total square-sector trace of -8, including sign/parity multiplicities;
* the cubic color identity, which turns the weighted trace into twice the
  number of triangle-free-colored vertices.

It is a necessary-condition ledger, not a graph-existence claim.
"""

from __future__ import annotations


EXPECTED = (
    (0, 1, 2), (0, 1, 4), (0, 1, 6), (0, 1, 8),
    (0, 2, 4), (0, 2, 6), (0, 2, 8),
    (0, 3, 2), (0, 3, 4), (0, 3, 6), (0, 3, 8),
    (1, 0, 3), (1, 0, 5),
)

EXPECTED_COLOR_COUNTS = {
    (0, 1, 2): 31, (0, 1, 4): 31, (0, 1, 6): 31, (0, 1, 8): 31,
    (0, 2, 4): 46, (0, 2, 6): 46, (0, 2, 8): 46,
    (0, 3, 2): 31, (0, 3, 4): 31, (0, 3, 6): 31, (0, 3, 8): 31,
    (1, 0, 3): 40, (1, 0, 5): 40,
}


def signed_multiplicity_values(multiplicity: int) -> range:
    """Possible (#positive - #negative) values for a sector."""
    return range(-multiplicity, multiplicity + 1, 2)


def main() -> int:
    survivors: list[tuple[int, int, int]] = []
    color_counts: dict[tuple[int, int, int], set[int]] = {}
    for m6 in range(16):
        for m3 in range(16 - m6):
            for mneg2 in range(16 - m6 - m3):
                residual_count = 15 - m6 - m3 - mneg2
                residual_sum = -7 - 6 * m6 - 3 * m3 + 2 * mneg2
                residual_square_sum = (
                    63 - 36 * m6 - 9 * m3 - 4 * mneg2
                )
                if residual_square_sum < 0:
                    continue
                if residual_count == 0:
                    if residual_sum != 0 or residual_square_sum != 0:
                        continue
                elif residual_sum**2 > residual_count * residual_square_sum:
                    continue
                colors = {
                    -(sign6 + 8 * sign3 + 27 * signneg2) // 2
                    for sign6 in signed_multiplicity_values(m6)
                    for sign3 in signed_multiplicity_values(m3)
                    for signneg2 in signed_multiplicity_values(mneg2)
                    if sign6 + 2 * sign3 + 3 * signneg2 == -8
                    and (sign6 + 8 * sign3 + 27 * signneg2) % 2 == 0
                }
                if colors:
                    survivors.append((m6, m3, mneg2))
                    color_counts[(m6, m3, mneg2)] = colors

    if tuple(survivors) != EXPECTED:
        raise AssertionError(f"unexpected moment ledger: {survivors}")
    if any(mneg2 == 0 for _, _, mneg2 in survivors):
        raise AssertionError("a survivor unexpectedly avoids eigenvalue -2")
    observed_colors = {
        pattern: next(iter(colors))
        for pattern, colors in color_counts.items()
        if len(colors) == 1
    }
    if observed_colors != EXPECTED_COLOR_COUNTS:
        raise AssertionError(f"unexpected cubic color ledger: {color_counts}")
    if any(color_count <= 16 for color_count in observed_colors.values()):
        raise AssertionError("a rational square pattern survives the H16 color cap")
    print("columns: multiplicity(mu=6), multiplicity(mu=3), multiplicity(mu=-2)")
    for survivor in survivors:
        print(*survivor, "colored_vertices=", observed_colors[survivor])
    print(
        f"survivors={len(survivors)}; every survivor has mu=-2; "
        "every cubic color count exceeds 16"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
