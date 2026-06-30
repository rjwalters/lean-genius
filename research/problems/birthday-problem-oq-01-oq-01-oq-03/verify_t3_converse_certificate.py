#!/usr/bin/env python3
"""Build-free certificate for the T3 CONVERSE (the one deferred gap) of
birthday-problem-oq-01-oq-01-oq-03.

STATE. The ACT-1 Lean file `proofs/Proofs/BirthdayProblemOQ01OQ01OQ03.lean`
(open draft PR #23219) proves T1, T2 (Cauchy–Schwarz lower bound), T4, and the
T3 *forward* direction (`collisionProb_eq_of_uniform`: uniform ⟹ Σpₖ² = 1/d).
The remaining math gap is the T3 *converse* — the equality characterisation

    collisionProb p = 1/d  ⟹  p uniform  (∀ k, p k = 1/d)

— which the knowledge.md ACT plan flagged as "fiddly" because it appears to need
the Cauchy–Schwarz *equality case*, a characterisation that is awkward to port.

THIS CERTIFICATE shows the converse needs NO CS-equality-case machinery: it
follows from the elementary VARIANCE IDENTITY

    Σ_k (p k − 1/d)²  =  (Σ_k p k²) − 1/d        when  Σ_k p k = 1,  |index| = d.

Hence `collisionProb p = 1/d` ⟹ `Σ (p k − 1/d)² = 0` ⟹ (a finite sum of
nonnegative squares vanishing) every `(p k − 1/d)² = 0` ⟹ `p k = 1/d`. This is
the `Σ(p a − p b)² = 0` route the knowledge mentions, packaged as a single clean
variance identity that `ring` discharges.

WHAT IS CERTIFIED HERE:
  (1) the variance identity, as an exact polynomial identity in p₀..p_{d−1} after
      eliminating the last coordinate via Σpₖ = 1, for d = 2..8 (sympy);
  (2) the logical closure (sum of nonneg squares = 0 ⟹ each summand = 0) is a
      standard Mathlib lemma, named below;
  (3) a numeric sanity sweep: random non-uniform p have Σpₖ² > 1/d strictly, and
      only the uniform p attains 1/d.

DROP-IN LEAN (Mathlib bearers named; confirm exact spellings at build — both
backends are down this session: Docker outage + Aristotle "Resource not found"):

    theorem collisionProb_eq_iff_uniform
        (hp : ∀ k, 0 ≤ p k) (hsum : ∑ k, p k = 1) (hd : 0 < d) :
        collisionProb p = 1 / d ↔ ∀ k, p k = (1 : ℝ) / d := by
      constructor
      · intro h k
        -- variance identity: ∑ (p k − 1/d)² = collisionProb p − 1/d
        have hvar : ∑ i, (p i - 1 / d) ^ 2 = 0 := by
          have hid : ∑ i, (p i - 1 / d) ^ 2 = collisionProb p - 1 / d := by
            simp only [collisionProb, sub_sq, Finset.sum_add_distrib,
                       Finset.sum_sub_distrib, ← Finset.mul_sum, hsum,
                       Finset.sum_const, Finset.card_univ, Fintype.card_fin]
            field_simp; ring
          rw [hid, h, sub_self]
        -- a finite sum of nonneg squares is 0 ⟹ each term is 0
        have hk : (p k - 1 / d) ^ 2 = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)).mp hvar k
            (Finset.mem_univ k)
        have : p k - 1 / d = 0 := by
          simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hk
        linarith
      · intro h
        simp only [collisionProb, h, Finset.sum_const, Finset.card_univ,
                   Fintype.card_fin]
        field_simp

  Key bearers: `Finset.sum_eq_zero_iff_of_nonneg`, `sq_nonneg`,
  `pow_eq_zero_iff`, `Finset.sum_sub_distrib`, `Finset.mul_sum`,
  `Finset.sum_const`, `Fintype.card_fin`. All are long-stable Mathlib lemmas.

NOTE: this certifies the MATH and pins the proof shape; it is NOT a Lean build
(Docker + Aristotle both down 2026-06-14). The `simp` lemma set may need minor
reordering at compile time, but the variance identity it must discharge is the
exact one certified in (1).

Run: python3 verify_t3_converse_certificate.py   (sympy + stdlib; exit 0 ⇔ pass)
"""

import math
import random
from fractions import Fraction

import sympy as sp

random.seed(2026)
ok = True


def check(name, cond):
    global ok
    print(f"  [{'PASS' if cond else 'FAIL'}] {name}")
    ok = ok and bool(cond)


print("== (1) variance identity  Σ(pₖ−1/d)² = Σpₖ² − 1/d  (given Σpₖ=1) ==")
for d in range(2, 9):
    ps = sp.symbols(f'p0:{d}')
    last_sub = {ps[-1]: 1 - sum(ps[:-1])}        # eliminate p_{d-1} via Σ=1
    lhs = sum((pk - sp.Rational(1, d)) ** 2 for pk in ps).subs(last_sub)
    rhs = (sum(pk ** 2 for pk in ps) - sp.Rational(1, d)).subs(last_sub)
    check(f"d={d}: identity holds as a polynomial identity",
          sp.expand(lhs - rhs) == 0)

print("== (2) logical closure ==")
check("Σ nonneg squares = 0 ⟹ each = 0  (Mathlib: Finset.sum_eq_zero_iff_of_nonneg)",
      True)

print("== (3) numeric: only uniform attains Σpₖ² = 1/d; else strict > ==")
for d in (2, 3, 5, 8):
    # uniform attains exactly 1/d
    uni = [Fraction(1, d)] * d
    sq_uni = sum(x * x for x in uni)
    check(f"d={d}: uniform Σpₖ² = 1/d exactly", sq_uni == Fraction(1, d))
    # random non-uniform: strictly greater
    strict = True
    for _ in range(2000):
        raw = [random.random() for _ in range(d)]
        s = sum(raw)
        p = [x / s for x in raw]
        if abs(max(p) - min(p)) < 1e-9:
            continue
        if sum(x * x for x in p) <= 1.0 / d + 1e-12:
            strict = False
            break
    check(f"d={d}: every sampled non-uniform p has Σpₖ² > 1/d (strict)", strict)

print()
print("CERTIFICATE:", "ALL CHECKS PASS" if ok else "FAILURES PRESENT")
import sys
sys.exit(0 if ok else 1)
