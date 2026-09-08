#!/usr/bin/env python3
"""Exact calibration of the finite all-length integrality criterion."""

from fractions import Fraction
from itertools import product
from math import gcd
from pathlib import Path
import runpy


def multiply(a, b):
    result = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            result[i+j] += x*y
    return result


def mod4_square(p):
    r = [x % 2 for x in p[::2]]
    square = multiply(r, r)
    return all((x - (square[i] if i < len(square) else 0)) % 4 == 0
               for i, x in enumerate(p))


def square_root(p, limit):
    result = [Fraction(1)]
    for i in range(1, limit+1):
        result.append((Fraction(p[i] if i < len(p) else 0)
                       - sum(result[j]*result[i-j] for j in range(1, i))) / 2)
    return result


def moments_from_poly(p, n, limit):
    # Newton identities for P(t)=det(I-tA), including zero roots if deg P<n.
    moments = [n]
    for k in range(1, limit+1):
        value = -k*(p[k] if k < len(p) else 0)
        value -= sum(p[j]*moments[k-j] for j in range(1, min(k, len(p))))
        moments.append(value)
    return moments


def poly_from_moments(moments, n):
    result = [1]
    for k in range(1, n+1):
        numerator = -sum(result[k-j]*moments[j] for j in range(1, k+1))
        assert numerator % k == 0
        result.append(numerator // k)
    return result


def main():
    base = Path(__file__).parent
    nb = runpy.run_path(str(base / 'verify_nonbacktracking_positivity_audit.py'))
    control = runpy.run_path(str(base / 'binary_q4_fixed_free_disconnected_control.py'))
    rows = control['adjacency'](control['A_EDGES'])
    moments = nb['adjacency_moments'](rows, 16)
    p4 = poly_from_moments(moments, 16)
    assert mod4_square(p4)
    assert all(c.denominator == 1 for c in square_root(p4, 40))
    print('actual q4 characteristic polynomial: mod4 square PASS')

    ledger = runpy.run_path(str(base / 'verify_nonbip_connected_odd_power_mod4.py'))
    p16 = [1]
    for root in [16, -4, -4, -4, -4, 2, -1, -1]:
        p16 = multiply(p16, [1, -root])
    for a, count in ledger['PAIRS'].items():
        for _ in range(count):
            p16 = multiply(p16, [1, 0, -a])
    assert len(p16) == 257 and not mod4_square(p16)
    derived = moments_from_poly(p16, 256, 20)
    assert derived == [ledger['moment'](k) for k in range(21)]
    traces = nb['spectral_traces'](256, 16, lambda k: derived[k], 20)
    failures = [k for k in range(1, 21)
                if nb['primitive_count'](traces, k).denominator != 1]
    assert failures == [6, 12]
    print('old q16 ledger: mod4 square FAIL; nonintegral lengths through20:', failures)

    count = 0
    for coefficients in product(range(-2, 3), repeat=4):
        p = [1, *coefficients]
        verdict = mod4_square(p)
        root_integral = all(c.denominator == 1 for c in square_root(p, 12))
        moments = moments_from_poly(p, 4, 12)
        traces = nb['spectral_traces'](4, 4, lambda k: moments[k], 12)
        cycle_integral = all(nb['primitive_count'](traces, k).denominator == 1
                             for k in range(1, 13))
        # The rotation divisor sum equals the sum of ordinary Euler exponents.
        # Include degrees1,2 explicitly for these nongraph polynomial controls.
        walk_parity = True
        for length in range(1, 13):
            numerator = sum(sum(gcd(j, length//d) == 1
                                for j in range(1, length//d+1)) * moments[d]
                            for d in range(1, length+1) if length % d == 0)
            walk_parity &= numerator % (2*length) == 0
        assert verdict == root_integral == cycle_integral == walk_parity, p
        count += 1
    assert not mod4_square([1, 0, 0, 0, 2])
    root = square_root([1, 0, 0, 0, 2], 8)
    assert root[4] == 1 and root[8] == Fraction(-1, 2)
    print(f'{count} small polynomial controls: finite criterion, roots, and cycle tests agree')
    print('All-length proof is in the companion note; no A-REG exclusion claimed.')


if __name__ == '__main__':
    main()
