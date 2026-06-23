#!/usr/bin/env python3
"""
Durable numerical certificate for ptolemys-theorem-oq-03
========================================================

Sine addition formula from Ptolemy's theorem.

Construction (Ptolemy's own, used to build trig chord tables in the Almagest):
inscribe a quadrilateral A, B, C, D in a circle of diameter 1, with the
diagonal AC a diameter. Place (centre at origin, radius 1/2):

    A = (-1/2, 0),                 C = (1/2, 0),          so |AC| = 1,
    B = (1/2 cos 2a, 1/2 sin 2a),  D = (1/2 cos 2b, -1/2 sin 2b).

Then the inscribed angles are angle BAC = a, angle CAD = b, angle BAD = a + b
(B and D on opposite arcs). Since AC is a diameter, angle ABC = angle ADC = pi/2
(Thales), giving

    |AB| = cos a,  |BC| = sin a,  |AD| = cos b,  |CD| = sin b,
    |BD| = sin(a + b)            (chord = diameter * sin(inscribed angle) = sin).

Ptolemy's theorem |AC|*|BD| = |AB|*|CD| + |BC|*|AD| then reads

    sin(a + b) = cos a * sin b + sin a * cos b.

This script checks every relation directly from the coordinates (no trig
identity is assumed beyond the construction), over 20000 random (a, b) with
a, b > 0 and a + b < pi -- the range for which the inscribed-quadrilateral
construction is valid.

Run:  python3 verify_ptolemy_sine_addition.py
"""
import math
import random


def dist(P, Q):
    return math.hypot(P[0] - Q[0], P[1] - Q[1])


def main():
    maxerr_sides = maxerr_diag = maxerr_ptolemy = maxerr_identity = 0.0
    random.seed(0)
    n = 0
    for _ in range(20000):
        a = random.uniform(0.01, 1.5)
        b = random.uniform(0.01, 1.5)
        if a + b >= math.pi - 0.01:
            continue
        n += 1
        A = (-0.5, 0.0)
        C = (0.5, 0.0)
        B = (0.5 * math.cos(2 * a), 0.5 * math.sin(2 * a))
        D = (0.5 * math.cos(2 * b), -0.5 * math.sin(2 * b))
        AC, AB, BC = dist(A, C), dist(A, B), dist(B, C)
        AD, CD, BD = dist(A, D), dist(C, D), dist(B, D)
        maxerr_sides = max(maxerr_sides,
                           abs(AB - math.cos(a)), abs(BC - math.sin(a)),
                           abs(AD - math.cos(b)), abs(CD - math.sin(b)),
                           abs(AC - 1.0))
        maxerr_diag = max(maxerr_diag, abs(BD - math.sin(a + b)))
        maxerr_ptolemy = max(maxerr_ptolemy, abs(AC * BD - (AB * CD + BC * AD)))
        maxerr_identity = max(maxerr_identity,
                              abs(math.sin(a + b)
                                  - (math.sin(a) * math.cos(b)
                                     + math.cos(a) * math.sin(b))))

    print(f"trials: {n}")
    print(f"max err chord-as-sine (AB=cos a, BC=sin a, AC=1, ...): {maxerr_sides:.2e}")
    print(f"max err diagonal BD = sin(a+b):                        {maxerr_diag:.2e}")
    print(f"max err Ptolemy AC*BD = AB*CD+BC*AD:                   {maxerr_ptolemy:.2e}")
    print(f"max err derived identity sin(a+b)=sa cb+ca sb:         {maxerr_identity:.2e}")
    worst = max(maxerr_sides, maxerr_diag, maxerr_ptolemy, maxerr_identity)
    print("PASS" if worst < 1e-9 else "FAIL")
    return 0 if worst < 1e-9 else 1


if __name__ == "__main__":
    raise SystemExit(main())
