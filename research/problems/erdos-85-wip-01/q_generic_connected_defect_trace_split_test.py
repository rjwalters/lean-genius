#!/usr/bin/env python3
"""Integral-square-root trace test for NONBIP-CONNECTED control models.

Companion to q_generic_connected_defect_spectral_countermodel.py (sol-1).
That script shows the circulant D_q passes the determinant / spanning-tree
tests.  This script shows D_q FAILS the finer integral-square-root test.

Mechanism (orbit lemma, cf. Erdos85AbstractTraceEscape):
  A symmetric 0/1 with A^2 = (q-1) I + J - D and tr A = 0.  On a D-eigenspace
  of eigenvalue mu (dim k) A acts with eigenvalues +/- sqrt(q-1-mu).  If
  sqrt(q-1-mu) is NOT in Q(mu), the two signs are Galois conjugate, so they
  have equal multiplicity: k is even and the sector contributes 0 to every
  odd power trace.  Hence
      q + sum_{unpaired sectors} m_theta * theta = tr A = 0.

Checks performed for D_q (q = 4, 8):
  * deg minpoly(sqrt(q-1-mu)) == 2 * deg minpoly(mu)  <=> sqrt not in Q(mu)
    for every residual sector (exact, sympy);
  * the unpaired sectors cannot sum to -q;
  * q = 4 additionally: exhaustive over all sign splits, no integer charpoly
    with trace 0.

Result: D_4 and D_8 are killed.  The uniform-q statement is NOT claimed.
"""
from __future__ import annotations

import argparse
import itertools
import math
from collections import Counter

import numpy as np
import sympy as sp


def gens(q):
    n = q * q
    g = {n // 2}
    for s in [1] + [2 ** k for k in range(1, 20) if 2 ** k <= q - 4]:
        g |= {s, n - s}
    return g


def orbit_test(q):
    n = q * q
    g = gens(q)
    x = sp.symbols('x')
    assert len(g) == q - 1
    classes = {}
    for j in range(n):
        m = sum(sp.cos(2 * sp.pi * s * j / n) for s in g)
        classes.setdefault(round(float(m), 9), []).append(m)
    unpaired = []  # (theta, mult) with sqrt(q-1-mu) in Q(mu)
    bad = []
    for key, ms in sorted(classes.items()):
        k = len(ms)
        m = ms[0]
        if abs(key - (q - 1)) < 1e-9:
            assert k == 1  # principal sector, theta = q
            continue
        off = sp.nsimplify(q - 1 - m)
        dm = sp.degree(sp.minimal_polynomial(m, x), x)
        dt = sp.degree(sp.minimal_polynomial(sp.sqrt(off), x), x)
        if dt == 2 * dm:
            if k % 2:
                bad.append(('odd paired sector', key, k))
        else:
            assert dt == dm
            unpaired.append((float(sp.sqrt(off)), k))
    reach = {0.0}
    for th, k in unpaired:
        reach = {r + th * (2 * a - k) for r in reach for a in range(k + 1)}
    trace_ok = any(abs(r + q) < 1e-9 for r in reach)
    print(f"q={q} order={n} residual_classes={len(classes) - 1} "
          f"unpaired={[(round(t, 6), k) for t, k in unpaired]} "
          f"paired_odd_violations={len(bad)} trace_zero_feasible={trace_ok}")
    return (not bad) and trace_ok


def exhaustive_q4():
    q = 4
    n = 16
    g = gens(q)
    mu = [sum(math.cos(2 * math.pi * s * j / n) for s in g) for j in range(n)]
    c = Counter(round(m, 7) for m in mu)
    classes = [(m, k) for m, k in c.items() if abs(m - 3) > 1e-6]
    thetas = [(math.sqrt(3 - m), k) for m, k in classes]
    good = 0
    for a in itertools.product(*[range(k + 1) for _, k in thetas]):
        eig = [q]
        for (t, k), ai in zip(thetas, a):
            eig += [t] * ai + [-t] * (k - ai)
        if abs(sum(eig)) > 1e-6:
            continue
        p = np.poly(eig)
        if np.all(np.abs(p - np.round(p)) < 1e-5):
            good += 1
    print(f"q=4 exhaustive sign splits with tr=0 and integer charpoly: {good}")
    return good == 0


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--q', type=int, nargs='*', default=[4, 8])
    args = ap.parse_args()
    killed = 0
    for q in args.q:
        if not orbit_test(q):
            killed += 1
    if 4 in args.q:
        exhaustive_q4()
    print(f"verified_trace_split_kills={killed}/{len(args.q)}")
