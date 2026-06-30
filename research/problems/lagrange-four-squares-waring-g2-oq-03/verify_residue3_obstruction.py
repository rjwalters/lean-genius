#!/usr/bin/env python3
"""
Hardening certificate for the residue-3 carve-out in the corrected sufficiency
split (ThreeSquaresSufficiencyCorrected.lean).

Two claims are tested at scale with exact integer arithmetic:

  (O) OBSTRUCTION.  For every 4-free, non-excluded core m with m % 8 == 3, the
      monolithic Dirichlet witness
            exists d>0 with p = d*m - 1 prime and legendreSym p (-d) = 1
      has NO solution, for ANY d (searched far beyond the d<300 of the prior
      script).  This is what *forces* the separate Residue3Property route: the
      single-witness lemma `dirichlet_key_lemma` provably cannot reach m≡3 (8).

  (W) WITNESS SANITY.  Conversely, for m % 8 in {1,2,5,6} a witness DOES exist
      (so the carve-out is exactly the residue-3 class, nothing more).

A clean analytic reduction is also checked numerically:

  (R) Since p = d*m - 1 ≡ -1 (mod m), we have d ≡ m^{-1} (mod p), hence
            legendreSym p (-d) == legendreSym p (-m).
      So the witness condition is equivalent to "-m is a QR mod p". This makes
      the obstruction transparent: it is a statement about which primes p ≡ -1
      (mod m) have -m as a QR, i.e. a fixed congruence class mod 8 interacting
      with reciprocity.

  (RES3) Residue3Property holds (an odd t with (m - t^2)/2 prime, % 4 != 3) for
      every m % 8 == 3, m > 3, in range.  Also reports the *quadratic-deficit*
      nature: the successful (m - t^2)/2 do NOT lie in one linear AP, so plain
      Dirichlet-in-AP does not by itself discharge it (scoping note).
"""
import sys
from sympy import isprime


def is_excluded(n):
    while n % 4 == 0:
        n //= 4
    return n % 8 == 7


def legendre(a, p):  # p odd prime, returns 1 / -1 / 0
    a %= p
    if a == 0:
        return 0
    return 1 if pow(a, (p - 1) // 2, p) == 1 else -1


def witness_exists(m, dmax):
    """exists d in [1,dmax] with p=d*m-1 prime and legendreSym p (-d)=1."""
    for d in range(1, dmax + 1):
        p = d * m - 1
        if p > 2 and p % 2 == 1 and isprime(p):
            if legendre(-d, p) == 1:
                return (d, p)
    return None


def residue3_witness(m):
    t = 1
    while t * t <= m:
        rem = m - t * t
        if rem % 2 == 0:
            mm = rem // 2
            if mm >= 2 and isprime(mm) and mm % 4 != 3:
                return (t, mm)
        t += 2
    return None


def main():
    M_MAX = int(sys.argv[1]) if len(sys.argv) > 1 else 60000
    DMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 4000

    obstruction_violations = []   # m%8=3 cores where a witness DOES exist (want none)
    identity_violations = []      # where legendreSym p (-d) != legendreSym p (-m)
    good_residue_no_witness = []  # m%8 in {1,2,5,6} with NO witness up to DMAX (want none)
    res3_failures = []            # m%8=3, m>3 with no quadratic-deficit prime (want none)
    deficit_residues = set()      # mod-4 / mod-8 classes hit by successful (m-t^2)/2

    n_res3 = 0
    n_good = 0
    for m in range(2, M_MAX):
        if m % 4 == 0 or is_excluded(m):
            continue
        r = m % 8
        if r == 3:
            if m > 3:
                n_res3 += 1
                w = residue3_witness(m)
                if w is None:
                    res3_failures.append(m)
                else:
                    t, mm = w
                    deficit_residues.add(mm % 8)
            # obstruction: NO monolithic witness should exist for any d<=DMAX
            wit = witness_exists(m, DMAX)
            if wit is not None:
                d, p = wit
                # double-check the analytic identity on this witness
                if legendre(-d, p) != legendre(-m, p):
                    identity_violations.append((m, d, p))
                obstruction_violations.append((m, d, p))
        else:
            n_good += 1
            wit = witness_exists(m, DMAX)
            if wit is None:
                good_residue_no_witness.append(m)
            else:
                d, p = wit
                if legendre(-d, p) != legendre(-m, p):
                    identity_violations.append((m, d, p))

    print(f"=== residue-3 obstruction certificate  (m < {M_MAX}, d <= {DMAX}) ===")
    print()
    print(f"[O] m%8==3 cores with a monolithic witness (want EMPTY): "
          f"{obstruction_violations[:10]}  count={len(obstruction_violations)}")
    print(f"[W] m%8 in {{1,2,5,6}} with NO witness up to d={DMAX} (want EMPTY): "
          f"{good_residue_no_witness[:10]}  count={len(good_residue_no_witness)} "
          f"(of {n_good} good-residue cores)")
    print(f"[R] witnesses violating legendreSym p(-d)==legendreSym p(-m) "
          f"(want EMPTY): {identity_violations[:5]}  count={len(identity_violations)}")
    print(f"[RES3] m%8==3, m>3 with NO quadratic-deficit prime (want EMPTY): "
          f"{res3_failures[:10]}  count={len(res3_failures)} (of {n_res3} residue-3 cores)")
    print(f"[RES3] residues mod 8 of the successful prime deficit mm=(m-t^2)/2: "
          f"{sorted(deficit_residues)}  "
          f"(mm == 1 mod 4 forced; spread over mod-8 => NOT one linear AP)")
    print()
    ok = (not obstruction_violations and not good_residue_no_witness
          and not identity_violations and not res3_failures)
    print("ALL CHECKS PASSED" if ok else "*** CHECK FAILED ***")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
