#!/usr/bin/env python3
"""Exact multiplicity audit for the Stage-1 Fourier/Gram spectrum proof."""

from collections import Counter


def main():
    # Represent a+b*sqrt(3) by the exact integer pair (a,b).
    two_cos = [
        (2, 0), (0, 1), (1, 0), (0, 0), (-1, 0), (0, -1),
        (-2, 0), (0, -1), (-1, 0), (0, 0), (1, 0), (0, 1),
    ]
    spectrum = Counter()
    for k, (real, radical) in enumerate(two_cos):
        base = (real - 3, radical)
        if k == 0:
            coupling = 8
        elif k in (4, 8):
            coupling = -4
        else:
            coupling = 0
        spectrum[base] += 12
        spectrum[(base[0] + 12 - coupling, base[1])] += 3
        spectrum[(base[0] + 12 + 3 * coupling, base[1])] += 1

    expected = Counter({
        (35, 0): 1, (12, 0): 6, (10, 0): 8, (9, 0): 8,
        (9, 1): 8, (9, -1): 8, (7, 0): 4, (3, 0): 3,
        (-1, 0): 12, (-2, 0): 24, (-3, 0): 24, (-4, 0): 26,
        (-5, 0): 12, (-3, 1): 24, (-3, -1): 24,
    })
    assert spectrum == expected
    assert sum(spectrum.values()) == 192
    assert sum(value[0] * multiplicity
               for value, multiplicity in spectrum.items()) == 0
    assert sum((value[0] ** 2 + 3 * value[1] ** 2) * multiplicity
               for value, multiplicity in spectrum.items()) == 192 * 35

    # The two rational odd-moment equations have the unique permitted sign
    # imbalance.  Here a is even in [-26,26], b odd in [-3,3].
    solutions = []
    for a in range(-26, 27, 2):
        for b in range(-3, 4, 2):
            if 13 + 4 * a + 3 * b == 0 and \
                    13 ** 3 + 4 ** 3 * a + 3 ** 3 * b == 1968:
                solutions.append((a, b))
    assert solutions == [(-4, 1)]
    # On the all-ones line (H,A)=(13,35).  On the rational ±4 and
    # ±3 sectors, A=12-H² is respectively -4 and 3.  Every remaining
    # H-sign pair is balanced, so it cancels from traces odd in H.
    a, b = solutions[0]
    trace_HA = 13 * 35 + (4 * a) * (-4) + (3 * b) * 3
    trace_HA2 = 13 * 35 ** 2 + (4 * a) * (-4) ** 2 + \
        (3 * b) * 3 ** 2
    assert trace_HA == 528
    assert trace_HA2 == 15696
    assert trace_HA // 2 == 264
    assert trace_HA2 // 2 == 7848
    print("STAGE1 SERVICE SPECTRUM EXACT AUDIT OK")


if __name__ == "__main__":
    main()
