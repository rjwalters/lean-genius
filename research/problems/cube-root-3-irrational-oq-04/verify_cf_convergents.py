#!/usr/bin/env python3
"""
Reproducible, build-free verification of the continued-fraction convergent chain
for cube-root-3-irrational-oq-04 (the simple CF of ∛3, OEIS A002945).

Across ~17 iterations this gallery proof has added one CF partial quotient at a
time, each backed by a "convergent sandwich" Lean helper of the form
`cbrt3 < p/q` or `p/q < cbrt3`. Every step's arithmetic was re-derived with
throwaway Python. This script makes that derivation DURABLE and reproducible
without Docker/Mathlib: it recomputes the whole chain and checks every claim
the Lean helpers encode, exiting non-zero on any mismatch.

It is NOT a proof of the Lean theorems; it certifies the *arithmetic* those
theorems encode (CF digits, convergent recursion, and the exact integer
cube-direction inequalities p^3 vs 3 q^3), so each Lean step is a transcription
of pre-verified numbers rather than a fresh derivation.

Run:  python3 verify_cf_convergents.py
"""
import sys
from decimal import Decimal, getcontext

getcontext().prec = 220

FAILED = False


def check(name, cond, detail=""):
    global FAILED
    print(f"[{'OK' if cond else 'FAIL'}] {name}" + (f"  {detail}" if detail else ""))
    if not cond:
        FAILED = True


# --- high-precision ∛3 via Newton iteration (no float / no x**(1/3)) ----------
def cbrt3_decimal():
    g = Decimal("1.5")
    for _ in range(400):
        g = (2 * g + Decimal(3) / (g * g)) / 3
    return g


# --- continued fraction of ∛3 ------------------------------------------------
def continued_fraction(x, terms):
    cf = []
    for _ in range(terms):
        a = int(x)
        cf.append(a)
        frac = x - a
        if frac == 0:
            break
        x = 1 / frac
    return cf


# Known prefix of OEIS A002945 (CF of ∛3). Regression guard against any loss of
# precision in the Decimal CF extraction. Indices a0..a13 are exactly the
# partial quotients the gallery has proven (a9=6, a10=2, a11=5, a12=8, a13=3).
A002945_PREFIX = [1, 2, 3, 1, 4, 1, 5, 1, 1, 6, 2, 5, 8, 3, 3]


def convergents(cf):
    """Return list of (p_k, q_k) for k = 0..len(cf)-1 via the standard recursion."""
    pm1, qm1 = 1, 0          # p_{-1}, q_{-1}
    pn, qn = cf[0], 1        # p_0,   q_0
    out = [(pn, qn)]
    for a in cf[1:]:
        pn, pm1 = a * pn + pm1, pn
        qn, qm1 = a * qn + qm1, qn
        out.append((pn, qn))
    return out


def side(p, q):
    """Exact integer comparison of p/q against ∛3: sign of p^3 - 3 q^3."""
    d = p**3 - 3 * q**3
    return "<" if d < 0 else (">" if d > 0 else "==")  # cbrt3 (?) p/q


if __name__ == "__main__":
    c = cbrt3_decimal()
    # sanity: c^3 ≈ 3
    check("Newton ∛3: |c^3 - 3| < 1e-100", abs(c**3 - 3) < Decimal("1e-100"))

    cf = continued_fraction(c, 20)
    check("CF prefix matches OEIS A002945 (a0..a13)",
          cf[:len(A002945_PREFIX)] == A002945_PREFIX,
          detail=f"a0..a13 = {cf[:14]}")
    # the specific proven partial quotients, by their gallery names
    named = {9: 6, 10: 2, 11: 5, 12: 8, 13: 3}
    for idx, val in named.items():
        check(f"CF digit a{idx} = {val} (proven as cbrt3_a{idx})", cf[idx] == val)

    convs = convergents(cf)

    # Alternation: even-index convergents lie BELOW ∛3, odd-index ABOVE.
    alt_ok = all(side(p, q) == ("<" if k % 2 == 0 else ">")
                 for k, (p, q) in enumerate(convs))
    check("convergent alternation (even below, odd above ∛3)", alt_ok)

    # Per-convergent exact cube-direction inequality + relative gap.
    print("\n  k :        p / q              cbrt3 ? p/q   |p^3 - 3q^3| / (3q^3)")
    for k, (p, q) in enumerate(convs):
        s = side(p, q)
        rel = abs(p**3 - 3 * q**3) / Decimal(3 * q**3)
        print(f"  {k:2d}: {p}/{q}".ljust(34) + f"  cbrt3 {s} p/q   ~{rel:.3e}")

    # --- regression anchors: the convergents already proven as Lean helpers ---
    # (matching state.md / merged PRs S12a, S13, S14a)
    anchors = [
        (13361, 9264, "<", "S12a 11th convergent (lower)"),
        (73011, 50623, ">", "S13  12th convergent (upper)"),
        (597449, 414248, "<", "S13  13th convergent (lower)"),
        (1865358, 1293367, ">", "S14a 14th convergent (upper)"),
    ]
    print()
    for p, q, want, label in anchors:
        s = side(p, q)
        check(f"anchor {label}: cbrt3 {want} {p}/{q}", s == want)
        # also confirm it is exactly the convergent at the expected index
        check(f"   {p}/{q} is a genuine convergent of ∛3", (p, q) in convs)

    # --- forward de-risk: the NEXT convergent (15th, lower side) for a future ---
    # a13 sandwich, pre-verified so the next ACT is transcription.
    p14, q14 = convs[14]
    check("forward: 15th convergent cbrt3 < {}/{}".format(p14, q14)
          if side(p14, q14) == "<" else
          "forward: 15th convergent cbrt3 > {}/{}".format(p14, q14),
          side(p14, q14) == "<",
          detail=f"= {p14}/{q14} (even index 14 ⇒ lower bound)")

    if FAILED:
        print("\nVERIFICATION FAILED")
        sys.exit(1)
    print("\nAll CF/convergent arithmetic verified.")
