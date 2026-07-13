#!/usr/bin/env python3
"""
S8 certificate for zsqrtd-neg-two-oq-02 (Legendre three-square sufficiency).

Substantiates the architectural finding that the registered, build-pending file
`proofs/Proofs/ThreeSquaresSingleAP.lean` lets the sufficiency proof collapse the
residue-3 carve-out FOR ODD CORES, while EVEN cores (n % 8 in {2, 6}, 4 // n)
are NOT served by the single-AP / odd-reciprocity branch.

Single-AP claim (ThreeSquaresSingleAP.legendreSym_neg_n_eq_one):
    for ODD n and any prime p with p % (4n) == 1,  legendreSym(p, -n) == 1.
Existence (exists_prime_eq_one_mod_four_mul): such a prime always exists
(Dirichlet on the always-admissible class 1 mod 4n, gcd(1,4n)=1).

This script checks, build-free:
  (A) the QR identity legendreSym(p, -n)=1 for the smallest prime p == 1 (mod 4n),
      over every ODD n in range  -> 0 mismatches expected;
  (B) that such a prime is found in range for every odd n (existence);
  (C) the coverage split: which non-excluded 4-free cores are ODD (single-AP
      handles) vs EVEN (n%8 in {2,6}, still need a separate witness).

Pure Python, no Docker, no Lean. Reproducible.
"""

from sympy import isprime, legendre_symbol


def is_excluded(n: int) -> bool:
    """n == 4^a (8b + 7) for some a,b >= 0  (the never-three-square forms)."""
    while n % 4 == 0:
        n //= 4
    return n % 8 == 7


def smallest_prime_one_mod(mod: int, cap: int = 2_000_000) -> int | None:
    """Smallest prime p with p % mod == 1."""
    p = 1 + mod
    while p < cap:
        if isprime(p):
            return p
        p += mod
    return None


def legendre_neg_n(p: int, n: int) -> int:
    """legendreSym(p, -n) as in Lean: value in {-1,0,1}."""
    return legendre_symbol((-n) % p, p)


def main() -> None:
    N = 4000
    qr_checked = qr_mismatch = 0
    existence_fail = []
    odd_cores = even_cores = 0
    even_examples = []

    for n in range(1, N + 1):
        # (C) coverage split over non-excluded 4-free cores
        if not is_excluded(n) and n % 4 != 0 and n > 1:
            if n % 2 == 1:
                odd_cores += 1
            else:  # 4 // n and even  =>  n % 8 in {2, 6}
                even_cores += 1
                if len(even_examples) < 12:
                    even_examples.append(n)

        # (A)+(B) single-AP QR identity, odd n only
        if n % 2 == 1:
            p = smallest_prime_one_mod(4 * n)
            if p is None:
                existence_fail.append(n)
                continue
            qr_checked += 1
            if legendre_neg_n(p, n) != 1:
                qr_mismatch += 1
                print(f"  QR MISMATCH n={n} p={p} legendreSym(p,-n)={legendre_neg_n(p,n)}")

    print(f"range 1..{N}")
    print(f"(A) odd n with QR identity checked : {qr_checked}")
    print(f"(A) QR mismatches (expect 0)       : {qr_mismatch}")
    print(f"(B) existence failures (expect 0)  : {len(existence_fail)}")
    print(f"(C) non-excluded 4-free ODD  cores : {odd_cores}  (single-AP covers)")
    print(f"(C) non-excluded 4-free EVEN cores : {even_cores}  (n%8 in 2,6; NOT covered)")
    print(f"(C) smallest even cores            : {even_examples}")
    ok = qr_mismatch == 0 and not existence_fail
    print("RESULT:", "PASS" if ok else "FAIL")


if __name__ == "__main__":
    main()
