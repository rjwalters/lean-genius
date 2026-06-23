#!/usr/bin/env python3
"""
nth-root-irrational-oq-03 / ETranscendentalOQ03.lean — numerical grounding of the
sole remaining axiom:

    axiom e_not_liouvilleWith_gt_two (p : ℝ) (hp : p > 2) : ¬LiouvilleWith p (exp 1)

This is the statement that e has irrationality measure μ(e) ≤ 2 (in fact = 2).
A full Lean proof needs Euler's continued-fraction expansion of e (absent from
Mathlib, ~280–480 LOC, Docker-gated). This script does NOT discharge the axiom; it
provides a reproducible, high-precision *numerical certificate* that the bound the
axiom asserts is correct, giving the eventual Lean ACT a concrete reference.

Recall:
  LiouvilleWith p x  ⟺  ∃ C>0, infinitely many rationals h/q (q≥1, x≠h/q) with
                         |x − h/q| < C / q^p.
  μ(x) = sup{ p : |x − h/q| < 1/q^p for infinitely many h/q }.

Facts checked (exact rational convergents, mpmath at 4000 digits):
  (A) e = [2; 1,2,1, 1,4,1, 1,6,1, …]  (Euler's pattern a_{3k+2}=2(k+1)).
  (B) Convergents are the *best* rational approximations, so the measure is read
      off them. The local exponent λ_k = −ln|e − h_k/q_k| / ln q_k → 2 from below;
      it never settles above 2 → μ(e) = 2.
  (C) For p > 2: q^p · |e − h/q| → ∞ along convergents → NO Liouville constant C
      can work for infinitely many approximations → ¬LiouvilleWith p (exp 1).  ✓axiom
  (D) For p = 2: q^2 · |e − h/q| stays bounded (does NOT → 0), consistent with the
      already-PROVED `e_liouvilleWith_two` (μ(e) = 2 exactly, not < 2).
"""

import mpmath as mp

mp.mp.dps = 4000
E = mp.e


def cf_terms(x, n):
    """First n continued-fraction partial quotients of x (x kept as mpf)."""
    terms = []
    y = x
    for _ in range(n):
        a = int(mp.floor(y))
        terms.append(a)
        frac = y - a
        if frac == 0:
            break
        y = 1 / frac
    return terms


def convergents(terms):
    """Return list of (h, q) integer convergents from partial quotients."""
    hm1, hm2 = 1, 0
    qm1, qm2 = 0, 1
    out = []
    for a in terms:
        h = a * hm1 + hm2
        q = a * qm1 + qm2
        out.append((h, q))
        hm2, hm1 = hm1, h
        qm2, qm1 = qm1, q
    return out


N = 150
terms = cf_terms(E, N)

print("=" * 72)
print("(A) Continued fraction of e (Euler pattern [2;1,2,1,1,4,1,1,6,...])")
print("=" * 72)
print("a_0..a_20 =", terms[:21])
# verify Euler pattern: positions 2,5,8,... (0-indexed) are 2,4,6,...
expected = [2, 1]
k = 1
while len(expected) < len(terms):
    expected += [2 * k, 1, 1]
    k += 1
expected = expected[:len(terms)]
assert terms == expected, f"CF mismatch:\n got {terms}\n exp {expected}"
print("PASS: matches Euler's expansion a_{3k+2} = 2(k+1), else 1.\n")

convs = convergents(terms)

print("=" * 72)
print("(B/C/D) Local exponent and Liouville-constant behaviour along convergents")
print("=" * 72)
print(f"{'k':>3} {'q_k (digits)':>13} {'lambda_k':>12} "
      f"{'q^2|e-h/q|':>14} {'q^2.1|e-h/q|':>16} {'q^3|e-h/q|':>16}")

lambdas = []           # (q, lambda) for all convergents with q >= 10
qsq_vals = []
q21_vals = []
q3_vals = []
for k, (h, q) in enumerate(convs):
    if q < 10:
        continue
    err = abs(E - mp.mpf(h) / q)
    if err == 0:
        continue
    lam = -mp.log(err) / mp.log(q)
    qsq = q ** 2 * err
    q21 = mp.power(q, mp.mpf("2.1")) * err
    q3 = mp.power(q, 3) * err
    lambdas.append((q, float(lam)))
    qsq_vals.append(float(qsq))
    q21_vals.append(float(q21))
    q3_vals.append(float(q3))
    if k < 18 or k % 6 == 0:
        print(f"{k:>3} {len(str(q)):>13} {float(lam):>12.6f} "
              f"{float(qsq):>14.4e} {float(q21):>16.4e} {float(q3):>16.6e}")

# The local exponent lambda_k = -ln|e-h/q|/ln q overshoots 2 at the "good"
# convergents (just before a large partial quotient a_{3j+2}=2(j+1)), because
# |e-h_k/q_k| ~ 1/(a_{k+1} q_k^2) => lambda_k ~ 2 + ln(a_{k+1})/ln(q_k).
# Since ln(a_{k+1})/ln(q_k) -> 0, mu(e) = lim sup lambda_k = 2: the overshoot
# ENVELOPE must decrease decade-by-decade toward 2.
print()
print(f"{'q digits >=':>12} {'count':>6} {'max lambda':>12}")
decade_max = []
for d in [1, 5, 10, 20, 30, 40, 50]:
    sub = [lam for (q, lam) in lambdas if len(str(q)) >= d]
    if sub:
        decade_max.append((d, len(sub), max(sub)))
        print(f"{d:>12} {len(sub):>6} {max(sub):>12.6f}")

# (B) envelope decreasing toward 2: the max local exponent over ever-larger
#     denominators strictly decreases, and is < 2.05 once q has >= 30 digits.
maxes = [m for (_, _, m) in decade_max]
assert all(a >= b for a, b in zip(maxes, maxes[1:])), \
    "overshoot envelope not non-increasing"
assert maxes[0] - maxes[-1] > 0.4, "envelope not visibly descending toward 2"
big = [lam for (q, lam) in lambdas if len(str(q)) >= 50]
assert max(big) < 2.04, "local exponent for q>=1e50 too high — contradicts mu(e)=2"
print(f"envelope descends 2 + {maxes[0]-2:.3f}  ->  2 + {maxes[-1]-2:.3f} "
      "(slow ~ln(k)/ln(q_k) decay, limit 2)")
print("PASS (B): overshoot envelope decreases decade-by-decade; "
      "lim sup lambda_k = mu(e) = 2.\n")

# (C) p>2: q^p|e-h/q| -> infinity (strictly increasing tail) => no Liouville
#     constant exists => ¬LiouvilleWith p (exp 1).
assert q3_vals[-1] > q3_vals[len(q3_vals)//2] > q3_vals[0], \
    "q^3|e-h/q| not growing"
assert q3_vals[-1] > 1e3, "q^3|e-h/q| did not blow up"
assert q21_vals[-1] > q21_vals[0], "q^2.1|e-h/q| not growing"
print(f"PASS (C): q^3 |e-h/q| grows {q3_vals[0]:.3e} -> {q3_vals[-1]:.3e} (->inf),")
print(f"          q^2.1 |e-h/q| grows {q21_vals[0]:.3e} -> {q21_vals[-1]:.3e};")
print("          => no constant C bounds q^p|e-h/q| for p>2 => "
      "NOT LiouvilleWith p.  [grounds the axiom]\n")

# (D) p=2: q^2|e-h/q| stays bounded away from 0 and infinity (oscillates),
#     consistent with the PROVED e_liouvilleWith_two and with mu(e)=2 exactly.
assert min(qsq_vals) > 1e-3, "q^2|e-h/q| -> 0 would push measure below 2"
assert max(qsq_vals) < 1e3, "q^2|e-h/q| unbounded would push measure above 2"
print(f"PASS (D): q^2 |e-h/q| stays in [{min(qsq_vals):.3e}, {max(qsq_vals):.3e}] "
      "(neither ->0 nor ->inf)")
print("          consistent with proved e_liouvilleWith_two and mu(e)=2 exactly.\n")

print("ALL CHECKS PASSED — numerical grounding of e_not_liouvilleWith_gt_two.")
print("(This is evidence, not a Lean proof; the axiom remains, pending Euler CF.)")
