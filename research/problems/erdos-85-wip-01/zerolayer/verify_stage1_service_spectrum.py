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
    mixed_moments = [13 * 35 ** k + (4 * a) * (-4) ** k +
                     (3 * b) * 3 ** k for k in range(9)]
    assert mixed_moments == [
        0, 528, 15696, 558480, 19504272, 682801488,
        23897389776, 836411128080, 29274379049232,
    ]
    trace_A3_rational = sum(
        (value[0] ** 3 + 9 * value[0] * value[1] ** 2) * multiplicity
        for value, multiplicity in spectrum.items())
    trace_A3_radical = sum(
        (3 * value[0] ** 2 * value[1] + 3 * value[1] ** 3) * multiplicity
        for value, multiplicity in spectrum.items())
    assert trace_A3_rational == 74880
    assert trace_A3_radical == 0
    trace_H2A2 = 12 * (192 * 35) + 192 * 35 ** 2 - trace_A3_rational
    assert trace_H2A2 == 240960

    # The diagonal orphan-block of A^3 is fixed character-by-character.
    # For A_z = alpha I + K, K=VV*, its diagonal is
    # alpha^3 + 9 alpha^2 + 3 alpha (K^2)_oo + (K^3)_oo.
    # The Gram cases C=8,-4,0 give respectively
    # ((K^2)_oo,(K^3)_oo)=(84,2928),(48,768),(36,432).
    expected_fourier_A3 = [
        (2684, 0), (162, 84), (244, 0), (162, 0), (272, 0),
        (162, -84), (-8, 0), (162, -84), (272, 0), (162, 0),
        (244, 0), (162, 84),
    ]

    def mul(left, right):
        # (a+b√3)(c+d√3)
        return (left[0] * right[0] + 3 * left[1] * right[1],
                left[0] * right[1] + left[1] * right[0])

    fourier_A3 = []
    for k, (real, radical) in enumerate(two_cos):
        alpha = (real - 3, radical)
        if k == 0:
            k2, k3 = 84, 2928
        elif k in (4, 8):
            k2, k3 = 48, 768
        else:
            k2, k3 = 36, 432
        alpha2 = mul(alpha, alpha)
        alpha3 = mul(alpha2, alpha)
        fourier_A3.append((
            alpha3[0] + 9 * alpha2[0] + 3 * k2 * alpha[0] + k3,
            alpha3[1] + 9 * alpha2[1] + 3 * k2 * alpha[1],
        ))
    assert fourier_A3 == expected_fourier_A3

    def inverse_diagonal_block(fourier):
        result = []
        for distance in range(7):
            # Pair characters k and 12-k, using the exact 2*cos table.
            rational = fourier[0][0] + (-1) ** distance * fourier[6][0]
            radical = 0
            for k in range(1, 6):
                term = mul(fourier[k], two_cos[(k * distance) % 12])
                rational += term[0]
                radical += term[1]
            assert radical == 0 and rational % 12 == 0
            result.append(rational // 12)
        return result

    diagonal_A3 = inverse_diagonal_block(fourier_A3)
    assert diagonal_A3 == [390, 264, 180, 229, 180, 180, 228]
    same_block_A2 = [3, 4, 6, 3, 3, 6]
    same_block_B2 = [12 * a2 + 35 ** 2 - a3
                     for a2, a3 in zip(same_block_A2, diagonal_A3[1:])]
    assert same_block_B2 == [997, 1093, 1068, 1081, 1081, 1069]
    mixed_row_norm_sq = 12 * 35 + 35 ** 2 - diagonal_A3[0]
    assert mixed_row_norm_sq == 1255
    mixed_row_distance_sq = [2 * mixed_row_norm_sq - 2 * inner
                             for inner in same_block_B2]
    assert mixed_row_distance_sq == [516, 324, 374, 348, 348, 372]

    fourier_A4 = []
    for k, (real, radical) in enumerate(two_cos):
        alpha = (real - 3, radical)
        alpha2 = mul(alpha, alpha)
        alpha3 = mul(alpha2, alpha)
        alpha4 = mul(alpha3, alpha)
        if k == 0:
            k2, k3, k4 = 84, 2928, 105024
        elif k in (4, 8):
            k2, k3, k4 = 48, 768, 12288
        else:
            k2, k3, k4 = 36, 432, 5184
        fourier_A4.append((
            alpha4[0] + 4 * 3 * alpha3[0] + 6 * k2 * alpha2[0] +
            4 * k3 * alpha[0] + k4,
            alpha4[1] + 4 * 3 * alpha3[1] + 6 * k2 * alpha2[1] +
            4 * k3 * alpha[1],
        ))
    diagonal_A4 = inverse_diagonal_block(fourier_A4)
    assert diagonal_A4 == [10023, 7920, 7438, 7992, 7273, 7272, 7992]
    difference_A_energy = [
        2 * ((12 * diagonal_A3[0] - diagonal_A4[0]) -
             (12 * diagonal_A3[d] - diagonal_A4[d]))
        for d in range(1, 7)
    ]
    assert difference_A_energy == [-1182, -130, -198, -460, -462, -174]
    same_block_A = [1, 0, 0, 0, 0, 0]
    forced_support_mass = [12 * adjacent + 35 - a2
                           for adjacent, a2 in zip(same_block_A,
                                                   same_block_A2)]
    assert forced_support_mass == [44, 31, 29, 32, 32, 29]

    # Exact quotient action.  Rows are source omitted types and columns are
    # target types.  The sparse-type involution is (01)(23).
    paired = [1, 0, 3, 2]
    quotient_H = [[1 if target == paired[source] else 4
                   for target in range(4)] for source in range(4)]
    quotient_A = [[11 if source == target else 8
                   for target in range(4)] for source in range(4)]
    quotient_B = [[sum(quotient_H[source][middle] *
                       quotient_A[middle][target] for middle in range(4))
                   for target in range(4)] for source in range(4)]
    assert quotient_B == [[107 if source == paired[target] else 116
                           for target in range(4)] for source in range(4)]
    assert all(sum(row) == 455 for row in quotient_B)

    # For every component e and color r, H c_(e,r)=3*1+O_(pi(e)) and
    # H L_e=9*1+3*O_(pi(e)).  Apply H to
    # A c_(e,r)=12c_(e,r)-3L_e+8*1.
    for source in range(4):
        for component in range(4):
            paired_indicator = int(source == paired[component])
            h_color = 3 + paired_indicator
            h_linked = 9 + 3 * paired_indicator
            b_color = 12 * h_color - 3 * h_linked + 8 * 13
            assert b_color == 113 + 3 * paired_indicator
    print("STAGE1 SERVICE SPECTRUM EXACT AUDIT OK")


if __name__ == "__main__":
    main()
