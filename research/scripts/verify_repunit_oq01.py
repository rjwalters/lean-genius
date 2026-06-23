#!/usr/bin/env python3
"""Numerical certificate for repunit-oq-01 (Proofs/RepunitDivisibilityOQ01.lean).

Checks, by brute force, the two arithmetic facts the Lean proof rests on:

  1. repunit_dvd_iff:  R_b(m) | R_b(n)  <->  m | n   (base b >= 2)
  2. pred_mul_repunit_add_one:  (b - 1) * R_b(n) + 1 = b ^ n

where R_b(n) = sum_{i<n} b^i.  A clean run prints "OK" and exits 0.
"""

def R(b, n):
    return sum(b ** i for i in range(n))

def main():
    B_RANGE = range(2, 13)   # bases 2..12
    EXP = range(0, 25)       # exponents 0..24

    dvd_fail = []
    for b in B_RANGE:
        for m in EXP:
            Rm = R(b, m)
            for n in EXP:
                lhs = (R(b, n) % Rm == 0) if Rm != 0 else (R(b, n) == 0)
                rhs = (n % m == 0) if m != 0 else (n == 0)
                if lhs != rhs:
                    dvd_fail.append((b, m, n))

    bridge_fail = [(b, n) for b in range(1, 13) for n in EXP
                   if (b - 1) * R(b, n) + 1 != b ** n]

    assert not dvd_fail, f"repunit_dvd_iff counterexamples: {dvd_fail[:10]}"
    assert not bridge_fail, f"bridge identity fails: {bridge_fail[:10]}"
    print("OK: repunit_dvd_iff and (b-1)*R_b(n)+1 = b^n verified for "
          "2<=b<=12, m,n<=24")

if __name__ == "__main__":
    main()
