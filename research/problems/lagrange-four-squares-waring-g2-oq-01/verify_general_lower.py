#!/usr/bin/env python3
"""Durable numeric certificate for the GENERAL Waring lower bound.

Companion to `proofs/Proofs/LagrangeFourSquaresWaringG2OQ01General.lean`
(theorem `waring_lower_general`).

Claim (unconditional, elementary half of Waring's problem):
    For every k >= 1, with M = 2^k and Q = floor((3/2)^k) = 3^k // 2^k,
    the witness  n_k = Q*M - 1  is NOT a sum of  s = M + Q - 3  perfect
    k-th powers.  Hence  g(k) >= M + Q - 2 = 2^k + floor((3/2)^k) - 2.

This script certifies, exactly (Python big ints, no floats):
  (a) Q*M <= 3^k  (so n_k = Q*M - 1 < 3^k), i.e. the ONLY k-th powers
      <= n_k are 0, 1, 2^k  -- the uniform structural fact the Lean proof
      exploits;
  (b) the minimum number of k-th powers summing to n_k equals M + Q - 2,
      so a representation with s = M + Q - 3 summands is infeasible
      ("miss by exactly 1");
  (c) the predicted g(k) matches OEIS A002804 for every tabulated k.

Run:  python3 verify_general_lower.py
"""

A002804 = {1: 1, 2: 4, 3: 9, 4: 19, 5: 37, 6: 73, 7: 143,
           8: 279, 9: 548, 10: 1079, 11: 2132, 12: 4223}


def min_kth_powers_for_witness(k: int) -> int:
    """Min number of k-th powers summing to n_k = (3^k//2^k)*2^k - 1.

    Since the only admissible k-th powers <= n_k are {0, 1, 2^k}, a
    representation uses c2 copies of 2^k and c1 = n_k - c2*2^k copies of 1
    (c0 zeros are free).  Minimise c1 + c2 over 0 <= c2 <= Q.
    """
    M = 2 ** k
    Q = (3 ** k) // M
    n = Q * M - 1
    best = None
    for c2 in range(0, Q + 1):
        rem = n - c2 * M
        if rem < 0:
            break
        c1 = rem  # rem must be made of 1's
        cnt = c1 + c2
        if best is None or cnt < best:
            best = cnt
    return best


def certify(kmax: int = 30) -> bool:
    ok = True
    print(f"{'k':>3} {'M=2^k':>10} {'Q':>8} {'n_k=Q*M-1':>14} "
          f"{'g(k)=M+Q-2':>12} {'A002804':>8} {'QM<=3^k':>8} "
          f"{'min#':>10} {'match':>6}")
    for k in range(1, kmax + 1):
        M = 2 ** k
        Q = (3 ** k) // M
        n = Q * M - 1
        g = M + Q - 2
        qm_le = Q * M <= 3 ** k
        assert n < 3 ** k, f"n_k not < 3^k at k={k}"
        mn = min_kth_powers_for_witness(k)
        match = (mn == g)
        known = A002804.get(k, "-")
        oeis_ok = (known == "-") or (known == g)
        print(f"{k:>3} {M:>10} {Q:>8} {n:>14} {g:>12} {str(known):>8} "
              f"{str(qm_le):>8} {mn:>10} {str(match):>6}")
        if not (qm_le and match and oeis_ok):
            ok = False
            print(f"    !!! FAIL at k={k}: qm_le={qm_le} match={match} "
                  f"oeis_ok={oeis_ok}")
    return ok


if __name__ == "__main__":
    all_ok = certify(30)
    print()
    print("CERTIFICATE:", "PASS" if all_ok else "FAIL")
    raise SystemExit(0 if all_ok else 1)
