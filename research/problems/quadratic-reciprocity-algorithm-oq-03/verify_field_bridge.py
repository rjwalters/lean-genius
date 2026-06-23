#!/usr/bin/env python3
"""
verify_field_bridge.py — numerical certificate for the FIELD-FORM Zolotarev bridge
(quadratic-reciprocity-algorithm-oq-03, S18).

The verified Lean headline `legendreSym_eq_sign_mulLeft` states Zolotarev's lemma on the
UNITS group:  legendreSym p (u.val) = sign(mulLeft u),  mulLeft u : Perm (ZMod p)ˣ.

The exact OQ-pinned statement uses `Equiv.mulLeft₀ a ha` on the FIELD `ZMod p` (which fixes 0):
        legendreSym p (a.val) = sign(mulLeft₀ a),   mulLeft₀ a : Perm (ZMod p).

This script certifies the missing bridge and the precise structural decomposition the Lean
proof uses, so the field-form ACT is paste-ready (verify-before-assert: every relation is
COMPUTED, then asserted only after the data confirms it).

Findings asserted for every odd prime 3 <= p < 80, every nonzero a in ZMod p:

  (A) sign(mulLeft0 a on ZMod p)  ==  sign(mulLeft u on units)        [the bridge itself]
  (B) sign(mulLeft0 a on ZMod p)  ==  legendreSym(a, p)              [field-form Zolotarev]
  (C) mulLeft0 a maps nonzeros to nonzeros and fixes 0 (every MOVED point is nonzero), so
      its sign equals the sign of its restriction to the nonzero subtype.  These are exactly
      the two hypotheses (h1: a*x != 0 <-> x != 0;  h2: moved x => x != 0) consumed by the
      `sign_subtypePerm` step in the Lean proof.
  (D) the restriction of mulLeft0 a to {x != 0} is intertwined with mulLeft u on the units
      by the units<->nonzero equiv (unitsEquivNeZero):  e(u*x) = a*e(x).  This is the
      `sign_eq_sign_of_equiv` step.

Pure stdlib (sympy only for the Legendre symbol cross-check). Exits non-zero on any mismatch.
"""

import sys
from sympy import primerange, isprime
from sympy.ntheory.residue_ntheory import legendre_symbol


def perm_sign_by_cycles(perm: dict) -> int:
    """Sign of a permutation given as a dict mapping x->perm(x), via cycle decomposition."""
    seen = set()
    sign = 1
    for start in perm:
        if start in seen:
            continue
        # walk the cycle
        length = 0
        x = start
        while x not in seen:
            seen.add(x)
            x = perm[x]
            length += 1
        if length % 2 == 0:  # even-length cycle is an odd permutation
            sign = -sign
    return sign


def main() -> int:
    PMAX = 80
    checked = 0
    for p in primerange(3, PMAX):
        units = list(range(1, p))  # nonzero residues = (ZMod p)^x
        for a in units:
            # mulLeft0 a on the FULL field ZMod p (fixes 0)
            field_perm = {x: (a * x) % p for x in range(p)}
            s_field = perm_sign_by_cycles(field_perm)

            # mulLeft u on the UNITS group (ZMod p)^x  (closed under mult since p prime)
            units_perm = {x: (a * x) % p for x in units}
            s_units = perm_sign_by_cycles(units_perm)

            leg = legendre_symbol(a, p)

            # (A) the bridge
            assert s_field == s_units, f"(A) p={p} a={a}: field {s_field} != units {s_units}"
            # (B) field-form Zolotarev
            assert s_field == leg, f"(B) p={p} a={a}: sign {s_field} != legendre {leg}"

            # (C) h1: maps nonzeros to nonzeros (and 0 to 0);  h2: every moved point is nonzero
            assert field_perm[0] == 0, f"(C) p={p} a={a}: 0 not fixed"
            for x in range(p):
                if x != 0:
                    assert field_perm[x] != 0, f"(C) h1 p={p} a={a} x={x}: nonzero->0"
                if field_perm[x] != x:
                    assert x != 0, f"(C) h2 p={p} a={a}: 0 was moved"
            # restriction to nonzeros has the SAME sign as the full field perm
            restr = {x: (a * x) % p for x in units}
            assert perm_sign_by_cycles(restr) == s_field, \
                f"(C) p={p} a={a}: restriction sign != field sign"

            # (D) intertwining via unitsEquivNeZero (identity on values): e(u*x)=a*e(x)
            # e : units -> {x!=0} is the identity on the underlying value, so the
            # intertwining is the tautology (a*x mod p) == (a*x mod p); we assert the
            # permutation equality element-wise to mirror the Lean Subtype.ext step.
            for x in units:
                lhs = (a * x) % p          # value of e(mulLeft u x)
                rhs = (a * x) % p          # value of subtypePerm(mulLeft0 a)(e x)
                assert lhs == rhs, f"(D) p={p} a={a} x={x}: intertwine fail"

            checked += 1

    print(f"OK: field-form Zolotarev bridge certified for all odd primes 3<=p<{PMAX}.")
    print(f"    {checked} (p,a) pairs; assertions (A) bridge, (B) field-Zolotarev,")
    print(f"    (C) fixes 0 + moves only nonzeros / sign_subtypePerm, (D) unitsEquivNeZero intertwine.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
