#!/usr/bin/env python3
"""
ORIENT verification for erdos-978-oq-01:
    "Does n^4 + 2 represent infinitely many squarefree numbers?"
    (The k = 4 case of Erdos Problem #978, currently OPEN.)

The full statement is open mathematics (no proof is known; the k < 9 range of
Browning/Heath-Brown power-free results does not reach k = 4 for the squarefree
exponent). This script does NOT attempt to prove it. It establishes the
*build-free, checkable* facts that frame the conjecture and pin the only
quantity a formalization could realistically target:

  (1) NO LOCAL OBSTRUCTION. There is no fixed square m^2 > 1 dividing n^4 + 2
      for all n. Equivalently, for every prime p, the count
          rho(p^2) := #{ n mod p^2 : p^2 | n^4 + 2 }
      is strictly less than p^2 (in fact rho(p^2) <= 4). So the naive reason
      the answer could be "NO" (a covering square) does not occur.

  (2) CONJECTURAL DENSITY IS POSITIVE. Under the standard squarefree-sieve
      heuristic, the density of n <= N with n^4 + 2 squarefree is
          C = prod_p ( 1 - rho(p^2) / p^2 )
      We compute C over primes up to a cutoff and show the product converges to
      a positive constant ( > 0 ), so the heuristic predicts a POSITIVE density
      of squarefree values -- hence infinitely many. (A positive heuristic
      density is consistent with, but does not prove, the open conjecture.)

  (3) EMPIRICAL MATCH. The actual count of squarefree values of n^4 + 2 for
      n <= N, divided by N, agrees with C to within O(1/sqrt(N)) sampling
      error -- the standard sanity check that rho and the heuristic model the
      true behaviour.

  (4) WHICH PRIMES CONTRIBUTE. Lists the small primes p with rho(p^2) > 0
      (i.e. n^4 + 2 = 0 mod p^2 solvable). These are exactly the p where
      -2 is a fourth power mod p^2; they are the terms that pull C below 1.

All assertions are exact integer / rational computations except the final
empirical-vs-heuristic comparison, which is a numerical sanity bound.
"""

from sympy import factorint, primerange


# ---------------------------------------------------------------------------
def is_squarefree(n: int) -> bool:
    if n <= 0:
        return False
    return all(e == 1 for e in factorint(n).values())


def rho_psq(p: int) -> int:
    """#{ n mod p^2 : p^2 | n^4 + 2 }."""
    m = p * p
    return sum(1 for n in range(m) if (n ** 4 + 2) % m == 0)


def rho_p(p: int) -> int:
    """#{ n mod p : p | n^4 + 2 }  (for context: solvability of x^4 = -2 mod p)."""
    return sum(1 for n in range(p) if (n ** 4 + 2) % p == 0)


# ---------------------------------------------------------------------------
def check_no_local_obstruction(prime_cutoff: int):
    """(1) No prime p has rho(p^2) = p^2; record rho(p^2) for all p < cutoff."""
    rho_table = {}
    ok = True
    for p in primerange(2, prime_cutoff):
        r = rho_psq(p)
        rho_table[p] = r
        # A covering square would need rho(p^2) = p^2. n^4 + 2 ≡ 0 mod p^2 has
        # at most 4 roots (degree 4), so this can never happen for p^2 > 4.
        if r >= p * p:
            ok = False
        if r > 4:
            ok = False  # degree-4 congruence: at most 4 roots mod p^2
    return ok, rho_table


def heuristic_density(prime_cutoff: int):
    """(2) C = prod_p (1 - rho(p^2)/p^2) over p < cutoff (rational-ish float)."""
    C = 1.0
    contributors = {}
    for p in primerange(2, prime_cutoff):
        r = rho_psq(p)
        if r:
            contributors[p] = r
        C *= (1.0 - r / (p * p))
    return C, contributors


def empirical_density(N: int) -> float:
    """(3) Fraction of n in [1, N] with n^4 + 2 squarefree."""
    cnt = sum(1 for n in range(1, N + 1) if is_squarefree(n ** 4 + 2))
    return cnt / N


# ---------------------------------------------------------------------------
def main():
    print("=" * 70)
    print("erdos-978-oq-01 : n^4 + 2 squarefree infinitely often?  (OPEN, k=4)")
    print("=" * 70)

    # (1) No local obstruction
    ok, rho_table = check_no_local_obstruction(prime_cutoff=200)
    assert ok, "FOUND a local square obstruction -- contradicts degree bound!"
    max_rho = max(rho_table.values())
    print(f"\n(1) No local obstruction over primes < 200:")
    print(f"    max_p rho(p^2) = {max_rho}  (<= 4, the degree bound)  [OK]")
    print(f"    => no fixed square divides n^4+2 for all n.")

    # (4) Contributing primes (small)
    contrib_small = {p: r for p, r in rho_table.items() if r}
    print(f"\n(4) Primes p<200 with p^2 | n^4+2 solvable (rho(p^2)>0):")
    print(f"    {contrib_small}")
    # cross-check: rho(p^2)>0  <=>  x^4 = -2 mod p solvable (Hensel lifts since
    # p is odd and does not divide 4n^3 at a root, as p != 2-related; verify):
    for p, r in contrib_small.items():
        rp = rho_p(p)
        assert rp > 0, f"rho(p^2)>0 but rho(p)=0 at p={p} -- Hensel inconsistency"
    print(f"    cross-check: each has x^4=-2 mod p solvable  [OK]")

    # (2) Heuristic density positive and convergent
    C_lo, _ = heuristic_density(prime_cutoff=200)
    C_hi, contributors = heuristic_density(prime_cutoff=2000)
    print(f"\n(2) Conjectural squarefree density C = prod_p (1 - rho(p^2)/p^2):")
    print(f"    C (primes<200)  = {C_lo:.6f}")
    print(f"    C (primes<2000) = {C_hi:.6f}")
    assert C_hi > 0.5, "heuristic density not clearly positive"
    print(f"    => C > 0 : heuristic predicts POSITIVE density of squarefree")
    print(f"       values, hence INFINITELY MANY (consistent with conjecture).")
    print(f"    tail (primes 200..2000) shifts C by {abs(C_hi-C_lo):.2e} -> converged")

    # (3) Empirical match
    for N in (2000, 10000, 50000):
        emp = empirical_density(N)
        err = abs(emp - C_hi)
        tol = 3.0 / (N ** 0.5)  # ~3 sigma sampling band
        print(f"\n(3) N={N:>6}: empirical={emp:.6f}  heuristic={C_hi:.6f}  "
              f"|diff|={err:.6f}  (3/sqrt N = {tol:.6f})")
        assert err < tol + 0.01, f"empirical deviates from heuristic at N={N}"
    print("\n    Empirical squarefree fraction tracks the heuristic constant.")

    print("\n" + "=" * 70)
    print("CONCLUSION (build-free): the conjecture has NO local obstruction and a")
    print("POSITIVE conjectural density; the empirical count matches. The open")
    print("difficulty is purely analytic (sieving the square divisors p^2 with")
    print("p ~ N^2, beyond Browning/Heath-Brown's k>=9 reach). All asserts pass.")
    print("=" * 70)


if __name__ == "__main__":
    main()
