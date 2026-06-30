#!/usr/bin/env python3
"""
sqrt2-plus-sqrt3-plus-sqrt5-irrational-oq-02  —  Session 2 (ORIENT, sharpening)

Session 1 (PR #24220) framed the induction heart
    sqrt p_k  NOT in  K_{k-1} = Q(sqrt p_1, ..., sqrt p_{k-1})
as a black box certified by "minpoly degree doubles".  That is correct but it
is NOT the statement a Lean proof can induct on directly.  This session pins
down the EXACT formalizable elementary induction and certifies the two facts
that make it well-founded — the artifact the ~250-450 LOC Lean ACT must encode
(no multiquadratic degree theorem needed).

----------------------------------------------------------------------------
THE FORMALIZABLE INDUCTION (strengthened hypothesis).

  Let p_1 < p_2 < ... be primes and K_m = Q(sqrt p_1, ..., sqrt p_m), K_0 = Q.

  H(m):  for EVERY squarefree integer d > 1 whose prime factors are all
         OUTSIDE {p_1, ..., p_m},  sqrt(d)  is NOT in K_m.

  H(0) is "sqrt(d) irrational for squarefree d>1" (Mathlib: Nat.Prime.irrational_sqrt
  + the squarefree extension).  The OQ wants the special case
  H(k-1) applied to d = p_k.

  STEP  H(m-1) => H(m):  take squarefree d>1 with all prime factors outside
  {p_1..p_m}.  Suppose for contradiction sqrt(d) in K_m.  Every element of
  K_m = K_{m-1}(sqrt p_m) is  x = u + v*sqrt(p_m),  u, v in K_{m-1}
  (because sqrt p_m not in K_{m-1} by H(m-1) with d' = p_m, which is coprime to
  p_1..p_{m-1}, so [K_m : K_{m-1}] = 2 and {1, sqrt p_m} is a K_{m-1}-basis).
  Then
        d = x^2 = (u^2 + p_m v^2) + (2 u v) sqrt(p_m).
  Since d in K_{m-1} and {1, sqrt p_m} is a basis, the sqrt(p_m)-coordinate
  vanishes:  2 u v = 0,  so u = 0 or v = 0.

    * v = 0:  sqrt(d) = u in K_{m-1}.  But d is squarefree, coprime to
              p_1..p_{m-1}, contradicting H(m-1).
    * u = 0:  d = p_m v^2, so v^2 = d/p_m, i.e. sqrt(d * p_m) = v * p_m in
              K_{m-1}.  Now  d*p_m  is squarefree (d squarefree and coprime to
              p_m) and coprime to p_1..p_{m-1}, again contradicting H(m-1).

  Both branches hit H(m-1); the induction closes.  QED.

----------------------------------------------------------------------------
WHY THE NAIVE STATEMENT FAILS (the load-bearing observation):

  If one tried to induct on the unstrengthened  H'(m): "sqrt p_{m+1} not in K_m"
  (single new PRIME only), the u = 0 branch produces  sqrt(d * p_m) with a
  COMPOSITE radicand d*p_m = p_{m+1} * p_m, which H'(m-1) cannot discharge.
  The hypothesis MUST range over all coprime squarefree radicands, not just
  primes.  (Concretely: in the step for sqrt p_5 over Q(sqrt2,sqrt3,sqrt5),
  the u=0 branch needs sqrt(7*5)=sqrt35 not in Q(sqrt2,sqrt3), which is not a
  prime-radical statement.)

This script certifies, with EXACT arithmetic:
  (1) the square identity (u+v sqrt pm)^2 = (u^2+pm v^2) + 2uv sqrt(pm);
  (2) for each induction step, BOTH sub-radicands d and d*pm are squarefree and
      coprime to the smaller prime set (so H(m-1) applies to both);
  (3) the coprimality side condition is NOT removable: sqrt(p_i p_j) IS in
      K when both primes are in the generating set (e.g. sqrt6 in Q(sqrt2,sqrt3));
  (4) the non-membership itself, via exact minpoly-degree, for the radicands
      that appear in the two branches.
"""

import sys
import sympy as sp

X = sp.Symbol("x")


def squarefree_coprime(d, ps):
    """d>1 squarefree with no prime factor in the set ps."""
    if d <= 1:
        return False
    fac = sp.factorint(d)
    if any(e > 1 for e in fac.values()):
        return False
    return all(p not in ps for p in fac)


def sqrt_in_field(d, gens):
    """Exact test: sqrt(d) in Q(sqrt g : g in gens), via primitive element.
    True iff deg minpoly(sum sqrt gens + sqrt d) == deg minpoly(sum sqrt gens)."""
    base = sum(sp.sqrt(g) for g in gens) if gens else sp.Integer(0)
    if not gens:
        # sqrt(d) in Q iff d is a perfect square
        r = sp.sqrt(sp.Integer(d))
        return r.is_rational
    md = sp.minimal_polynomial(base, X).as_poly().degree()
    ext = sp.minimal_polynomial(base + sp.sqrt(d), X).as_poly().degree()
    return ext == md


def check_square_identity():
    print("== (1) square identity in K_{m-1}(sqrt p_m) ==")
    u, v, pm = sp.symbols("u v pm")
    lhs = sp.expand((u + v * sp.sqrt(pm)) ** 2)
    rhs = (u**2 + pm * v**2) + 2 * u * v * sp.sqrt(pm)
    assert sp.simplify(lhs - rhs) == 0
    print("   (u+v*sqrt(pm))^2 = (u^2 + pm v^2) + (2uv) sqrt(pm)   OK")
    print("   => rational/K_{m-1} value forces 2uv=0 (basis {1,sqrt pm})\n")


def check_branch_radicands(primes):
    print("== (2) each step: both branch radicands are squarefree & coprime ==")
    # step adding p_m, testing the OQ target radical d = p_{m+1}
    for m in range(1, len(primes) - 1):
        pm = primes[m - 1]            # newest generator sqrt p_m
        base = set(primes[: m - 1])   # p_1..p_{m-1}
        d = primes[m]                 # d = p_{m+1}: the prime we want to exclude
        b_v0 = squarefree_coprime(d, base)         # v=0 branch -> sqrt(d)
        b_u0 = squarefree_coprime(d * pm, base)    # u=0 branch -> sqrt(d*pm)
        print(
            f"   step pm={pm}, base={sorted(base)}, target d={d}: "
            f"v=0 -> sqrt({d}) [sf&coprime={b_v0}], "
            f"u=0 -> sqrt({d*pm}) [sf&coprime={b_u0}]"
        )
        assert b_v0 and b_u0, (m, d, pm)
    print("   OK: H(m-1) applies to BOTH branches; induction well-founded.\n")


def check_coprimality_necessary():
    print("== (3) coprimality side condition is NOT removable ==")
    # sqrt(p_i p_j) IS in the field when both primes generate it.
    assert sqrt_in_field(6, [2, 3]) is True, "sqrt6 should be in Q(sqrt2,sqrt3)"
    assert sqrt_in_field(15, [3, 5]) is True, "sqrt15 should be in Q(sqrt3,sqrt5)"
    print("   sqrt6 in Q(sqrt2,sqrt3)  = True   (6=2*3, factors in the set)")
    print("   sqrt15 in Q(sqrt3,sqrt5) = True   (15=3*5, factors in the set)")
    print("   => 'sqrt d not in K_m' is FALSE without the coprimality hypothesis.\n")


def check_nonmembership_branches():
    print("== (4) exact non-membership of the radicands that appear ==")
    cases = [
        # (d, gens, expect)   expect=False means sqrt(d) NOT in field (good)
        (7, [2, 3], False),       # v=0 branch for the sqrt5->sqrt7 style step
        (35, [2, 3], False),      # u=0 branch radicand 7*5
        (5, [2, 3], False),       # the OQ-relevant sqrt5 not in Q(sqrt2,sqrt3)
        (15, [2], False),         # u=0 branch radicand 5*3 over Q(sqrt2)
        (11, [2, 3, 5], False),   # next step
        (77, [2, 3, 5], False),   # 11*7 ... composite branch radicand
    ]
    for d, gens, expect in cases:
        got = sqrt_in_field(d, gens)
        tag = "in" if got else "NOT in"
        print(f"   sqrt({d}) {tag} Q({','.join('sqrt'+str(g) for g in gens)})   -> {got}")
        assert got == expect, (d, gens, got, expect)
    print("   OK: all branch radicals are genuinely outside the smaller field.\n")


if __name__ == "__main__":
    primes = [2, 3, 5, 7, 11, 13]
    check_square_identity()
    check_branch_radicands(primes)
    check_coprimality_necessary()
    check_nonmembership_branches()
    print("ALL CHECKS PASSED.")
    sys.exit(0)
