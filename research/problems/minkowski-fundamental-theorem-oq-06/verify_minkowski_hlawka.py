#!/usr/bin/env python3
"""
Durable verification for minkowski-fundamental-theorem-oq-06 (Minkowski-Hlawka).

The full theorem is NON-CONSTRUCTIVE and not formalizable from current Mathlib
(needs Siegel's mean-value theorem over SL_n(R)/SL_n(Z); see ORIENT notes). This
script does NOT prove the theorem. It pins down the *numerical content* of the
statement so the Lean target and its constants are unambiguous, and sanity-checks
the claimed lower bound against the classical densest-lattice-packing data.

What is checked:
  (A) Statement<->density derivation. The symmetric Minkowski-Hlawka statement
      "any symmetric S with vol(S) < 2*zeta(n) is avoided (nonzero) by some
      unimodular lattice" yields, with S a ball of radius 2r, the lattice
      packing-density lower bound
            delta_n >= zeta(n) / 2^(n-1).
      We verify vol(ball r) / vol(unit cell=1) = vol(S)/2^n = 2*zeta(n)/2^n
                                              = zeta(n)/2^(n-1).
  (B) Bound hierarchy: trivial saturation bound  2^(-n)  <=  MH bound
      <=  known densest lattice density delta_n^known,  for n where delta_n is known.
  (C) Improvement factor: MH / trivial = 2*zeta(n)  (-> 2 as n->infty since
      zeta(n) -> 1). MH improves the elementary maximal-packing bound by ~2x.

Run:  python3 verify_minkowski_hlawka.py
Requires: sympy (exact zeta/pi); falls back to float zeta via mpmath/math if absent.
"""

import math

try:
    from sympy import zeta, Rational, pi, factorial, nsimplify, simplify, N
    HAVE_SYMPY = True
except Exception:
    HAVE_SYMPY = False


def zeta_f(n: int) -> float:
    if HAVE_SYMPY:
        return float(zeta(n))
    # Euler-Maclaurin-free crude sum; n>=2 converges fast enough for a sanity check.
    s = 0.0
    for k in range(1, 200000):
        s += k ** (-n)
    return s


def mh_bound(n: int) -> float:
    """Minkowski-Hlawka lower bound on the densest LATTICE packing density, n>=2."""
    return zeta_f(n) / 2 ** (n - 1)


def trivial_bound(n: int) -> float:
    """Elementary maximal-packing (saturation) lower bound delta_n >= 2^-n."""
    return 2.0 ** (-n)


# Classical densest known LATTICE packing densities (fraction of space covered).
KNOWN = {
    1: 1.0,                                  # Z
    2: math.pi / math.sqrt(12),              # A2 hexagonal  ~0.90690
    3: math.pi / (3 * math.sqrt(2)),         # D3 / fcc      ~0.74048
    4: math.pi ** 2 / 16,                    # D4            ~0.61685
    5: math.pi ** 2 / (15 * math.sqrt(2)),   # D5            ~0.46526
    6: math.pi ** 3 / (48 * math.sqrt(3)),   # E6            ~0.37295
    7: math.pi ** 3 / 105,                   # E7            ~0.29530
    8: math.pi ** 4 / 384,                   # E8            ~0.25367
    24: math.pi ** 12 / math.factorial(12),  # Leech         ~0.0019296
}

EPS = 1e-12


def check_A_statement_density() -> bool:
    """vol(S)=2*zeta(n), S=ball(2r): density = vol(ball r) = vol(S)/2^n = zeta/2^(n-1)."""
    ok = True
    for n in range(2, 13):
        volS = 2.0 * zeta_f(n)               # symmetric threshold
        density_from_S = volS / 2 ** n       # ball radius r is ball(2r) scaled by 1/2
        target = mh_bound(n)
        if abs(density_from_S - target) > EPS * max(1.0, target):
            print(f"  [A] n={n}: derivation mismatch {density_from_S} vs {target}")
            ok = False
    return ok


def check_B_hierarchy() -> bool:
    ok = True
    for n in sorted(KNOWN):
        if n == 1:
            continue  # zeta(1) diverges; n=1 density is trivially 1
        triv, mh, kd = trivial_bound(n), mh_bound(n), KNOWN[n]
        if not (triv <= mh + EPS):
            print(f"  [B] n={n}: trivial {triv} !<= MH {mh}")
            ok = False
        if not (mh <= kd + EPS):
            print(f"  [B] n={n}: MH {mh} !<= known {kd}")
            ok = False
    return ok


def check_C_improvement() -> bool:
    ok = True
    for n in range(2, 25):
        ratio = mh_bound(n) / trivial_bound(n)
        if abs(ratio - 2.0 * zeta_f(n)) > 1e-9 * ratio:
            print(f"  [C] n={n}: ratio {ratio} != 2*zeta {2*zeta_f(n)}")
            ok = False
    # monotone approach to 2 from above as n grows
    if not (mh_bound(24) / trivial_bound(24) < mh_bound(2) / trivial_bound(2)):
        print("  [C] improvement factor not decreasing toward 2")
        ok = False
    return ok


def table():
    print(f"{'n':>3} {'2^-n (triv)':>13} {'zeta(n)/2^(n-1) (MH)':>22} "
          f"{'delta_n known':>14} {'MH/triv=2zeta(n)':>18}")
    for n in sorted(KNOWN):
        if n == 1:
            print(f"{n:>3} {trivial_bound(n):13.6g} {'(zeta diverges)':>22} "
                  f"{KNOWN[n]:14.6g} {'-':>18}")
            continue
        print(f"{n:>3} {trivial_bound(n):13.6g} {mh_bound(n):22.8g} "
              f"{KNOWN[n]:14.6g} {2*zeta_f(n):18.6g}")


if __name__ == "__main__":
    print(f"sympy available: {HAVE_SYMPY}\n")
    table()
    print()
    results = {
        "A statement<->density (delta=zeta/2^(n-1))": check_A_statement_density(),
        "B hierarchy 2^-n <= MH <= delta_known": check_B_hierarchy(),
        "C improvement factor MH/triv = 2*zeta(n)": check_C_improvement(),
    }
    print()
    allok = True
    for name, ok in results.items():
        print(f"[{'PASS' if ok else 'FAIL'}] {name}")
        allok = allok and ok
    print()
    print("ALL CHECKS PASSED" if allok else "SOME CHECKS FAILED")
    raise SystemExit(0 if allok else 1)
