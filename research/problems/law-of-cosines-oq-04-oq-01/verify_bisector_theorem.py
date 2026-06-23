#!/usr/bin/env python3
"""
law-of-cosines-oq-04-oq-01  (researcher-1) — the inner-product ANGLE-BISECTOR
THEOREM, closing the honesty gap flagged in Session 2.

Session 2 proved the internal-bisector LENGTH law assuming the cevian foot D
divides BC in ratio BD:DC = c:b (c=‖A-B‖, b=‖A-C‖), via the hypothesis
`hs : s·(b+c) = c`. Its honesty note: "that this ratio is the actual angle
bisector is a separate fact NOT proved here." This session proves exactly that
separate fact, in the same real-inner-product setting (any dimension), by the
same `ring`-after-expand technique the file already uses.

## Statement (inner-product angle-bisector theorem)
Let A,B,C ∈ V (real inner product space), c=‖A-B‖, b=‖A-C‖, both > 0, and let
        D = (b·B + c·C)/(b+c)        (the point dividing BC in ratio BD:DC = c:b).
Then the ray AD bisects ∠BAC, i.e. the two half-angles have equal cosine:
        ⟪B-A, D-A⟫ / ‖B-A‖ = ⟪C-A, D-A⟫ / ‖C-A‖
equivalently, the cleared (division-free, blackout-friendly) identity
        b · ⟪B-A, D-A⟫ = c · ⟪C-A, D-A⟫.                              (★)

## Proof (the exact `ring` certificate)
Put u = B-A, v = C-A, so ‖u‖²=c², ‖v‖²=b². Then D-A = (b·u + c·v)/(b+c), and
        b⟪u, D-A⟫ = (b/(b+c))(b‖u‖² + c⟪u,v⟫) = (bc/(b+c))(bc + ⟪u,v⟫),
        c⟪v, D-A⟫ = (c/(b+c))(b⟪u,v⟫ + c‖v‖²) = (cb/(b+c))(⟪u,v⟫ + cb),
which are EQUAL — using only ‖u‖²=c², ‖v‖²=b². So (★) is an identity (no further
hypothesis). The cleared form needs no `field_simp` (good under blackout).

This certifies: the ratio-c:b point of S2's length law IS the angle-bisector foot,
so the S2 length law `(b+c)²‖A-D‖² = bc((b+c)²-a²)` is genuinely the *internal
angle-bisector* length, not merely a cevian at a stipulated ratio.

Verification below (numpy, any dimension): (★) and the equal-cosine form to 1e-12,
plus the unit-vector-sum characterization (D-A ∥ û+v̂ with û=u/‖u‖, v̂=v/‖v‖).

Docker-independent.  Requires numpy.
"""
import numpy as np

rng = np.random.default_rng(20260615)


def trial(dim):
    A = rng.standard_normal(dim)
    B = rng.standard_normal(dim)
    C = rng.standard_normal(dim)
    c = np.linalg.norm(A - B)        # = ‖A-B‖, side opposite C
    b = np.linalg.norm(A - C)        # = ‖A-C‖, side opposite B
    if c < 1e-6 or b < 1e-6:
        return None
    D = (b * B + c * C) / (b + c)    # ratio BD:DC = c:b
    u = B - A
    v = C - A
    DA = D - A
    # (★) cleared identity
    lhs = b * np.dot(u, DA)
    rhs = c * np.dot(v, DA)
    err_star = abs(lhs - rhs)
    # equal-cosine form
    cos1 = np.dot(u, DA) / (np.linalg.norm(u) * np.linalg.norm(DA))
    cos2 = np.dot(v, DA) / (np.linalg.norm(v) * np.linalg.norm(DA))
    err_cos = abs(cos1 - cos2)
    # unit-vector-sum characterization: D-A parallel to û + v̂
    bis = u / np.linalg.norm(u) + v / np.linalg.norm(v)
    # parallelism: cross-Gram |DA|²|bis|² - <DA,bis>² = 0
    g = (np.dot(DA, DA) * np.dot(bis, bis) - np.dot(DA, bis) ** 2)
    err_par = abs(g)
    return err_star, err_cos, err_par


if __name__ == "__main__":
    print("law-of-cosines-oq-04-oq-01 :: inner-product ANGLE-BISECTOR theorem")
    print("=" * 68)
    print("D = (b·B + c·C)/(b+c) [ratio c:b]  ==>  b⟪B-A,D-A⟫ = c⟪C-A,D-A⟫")
    print("-" * 68)
    worst = {"star": 0.0, "cos": 0.0, "par": 0.0}
    ntot = 0
    for dim in (2, 3, 4, 5, 8):
        es = ec = ep = 0.0
        n = 0
        for _ in range(4000):
            r = trial(dim)
            if r is None:
                continue
            n += 1
            es = max(es, r[0]); ec = max(ec, r[1]); ep = max(ep, r[2])
        worst["star"] = max(worst["star"], es)
        worst["cos"] = max(worst["cos"], ec)
        worst["par"] = max(worst["par"], ep)
        ntot += n
        print(f"  dim={dim}: n={n:5d}  max|★|={es:.2e}  max|Δcos|={ec:.2e}  max|parallel-Gram|={ep:.2e}")
    print("-" * 68)
    ok = worst["star"] < 1e-10 and worst["cos"] < 1e-10 and worst["par"] < 1e-9
    print(f"total trials: {ntot}")
    print("RESULT:", "PASS — (★), equal-cosine, and û+v̂-parallelism all hold" if ok else "FAIL")
    print("=> the ratio-c:b cevian foot IS the internal angle-bisector foot, so")
    print("   Session-2's length law is genuinely the angle-bisector length law.")
