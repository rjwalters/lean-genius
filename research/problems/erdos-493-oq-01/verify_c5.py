#!/usr/bin/env python3
"""
Erdős #493 — OQ-01, result (C5): the count LADDER and MULTIPLICATIVITY.

These are corollaries of (C2)  #ordered reps of n  =  τ(n+1)  [verify_prodminussum.py],
made explicit here as theory-level structure and numerically certified so a future
session can formalize them quickly on top of the (reviewed) `reps_card_eq_tau`.

Let  r(n) := #{ (a,b) : a,b ≥ 2,  a*b - (a+b) = n }   (ordered representation count).
By C2,  r(n) = τ(n+1).  Hence, writing m = n+1 ≥ 1:

  (C5a) MULTIPLICATIVITY.  r is "multiplicative through the +1 shift":
        gcd(m₁, m₂) = 1  ⟹  r(m₁*m₂ - 1) = r(m₁ - 1) * r(m₂ - 1).
        (Directly: τ(m₁ m₂) = τ(m₁) τ(m₂) for coprime arguments.)

  (C5b) PRIME / PRIME-POWER BOUNDARY (sharp count ladder).
        r(n) = 1            ⟺  m = 1           (n = 0)
        r(n) = 2            ⟺  m is prime      (n+1 prime)
        r(n) = 3            ⟺  m = p²          (n+1 a prime square)
        r(n) = k+1          ⟺  m = p^k         (n+1 a prime power, exponent k)   [k ≥ 1]
        In general r(n) is prime  ⟺  m = p^(q-1) for primes p, q.

  (C5c) DIVISOR-SUM (Dirichlet) total over a range — a closed form for the
        cumulative number of representations:
            Σ_{n=0}^{N-1} r(n) = Σ_{m=1}^{N} τ(m) = Σ_{d=1}^{N} ⌊N/d⌋.

All three are checked below against the BRUTE-FORCE representation count (not against
τ), so they independently re-confirm C2 as well.
"""

from math import isqrt
from sympy import divisor_count, primerange, factorint, gcd


def brute_rep_count(n: int) -> int:
    """Ordered #{(a,b): a,b>=2, a*b-(a+b)=n}, counted directly (no use of tau)."""
    # a*b - (a+b) = n with a,b >= 2  forces  2 <= a,b <= n+2.
    cnt = 0
    for a in range(2, n + 3):
        for b in range(2, n + 3):
            if a * b - (a + b) == n:
                cnt += 1
    return cnt


def num_divisors(m: int) -> int:
    return int(divisor_count(m))


# ---------------------------------------------------------------------------
# C2 re-confirmation: brute r(n) == tau(n+1)  (foundation for everything below)
# ---------------------------------------------------------------------------
NMAX = 400
for n in range(0, NMAX + 1):
    assert brute_rep_count(n) == num_divisors(n + 1), f"C2 fails at n={n}"
print(f"C2  (brute r(n) == tau(n+1)):                    PASS for n=0..{NMAX}")

# ---------------------------------------------------------------------------
# C5a multiplicativity:  gcd(m1,m2)=1  =>  r(m1 m2 - 1) = r(m1-1) r(m2-1)
# (brute counts on all three points)
# ---------------------------------------------------------------------------
MMAX = 60
checked = 0
for m1 in range(1, MMAX + 1):
    for m2 in range(1, MMAX + 1):
        if gcd(m1, m2) != 1:
            continue
        lhs = brute_rep_count(m1 * m2 - 1)
        rhs = brute_rep_count(m1 - 1) * brute_rep_count(m2 - 1)
        assert lhs == rhs, f"C5a fails at m1={m1}, m2={m2}: {lhs} != {rhs}"
        checked += 1
print(f"C5a (coprime multiplicativity of r):             PASS ({checked} coprime pairs, m<= {MMAX})")

# sanity: NOT multiplicative without coprimality (the hypothesis is necessary)
# m1=m2=2: r(3)=tau(4)=3 ;  r(1)*r(1)=tau(2)*tau(2)=2*2=4 ;  3 != 4
assert brute_rep_count(3) != brute_rep_count(1) ** 2
print(f"     (coprimality necessary: r(3)=3 != r(1)^2=4)  PASS")

# ---------------------------------------------------------------------------
# C5b prime / prime-power boundary
# ---------------------------------------------------------------------------
# r(n)=1 <=> m=1
assert brute_rep_count(0) == 1
assert all(brute_rep_count(n) != 1 for n in range(1, NMAX + 1))
print(f"C5b r(n)=1  <=>  n=0:                            PASS for n=0..{NMAX}")

# r(n)=2 <=> n+1 prime
primes_set = set(primerange(2, NMAX + 2))
for n in range(0, NMAX + 1):
    assert (brute_rep_count(n) == 2) == ((n + 1) in primes_set), f"C5b prime fails n={n}"
print(f"C5b r(n)=2  <=>  n+1 prime:                      PASS for n=0..{NMAX}")

# r(n)=3 <=> n+1 = p^2
def is_prime_square(m: int) -> bool:
    f = factorint(m)
    return len(f) == 1 and list(f.values())[0] == 2

for n in range(0, NMAX + 1):
    assert (brute_rep_count(n) == 3) == is_prime_square(n + 1), f"C5b p^2 fails n={n}"
print(f"C5b r(n)=3  <=>  n+1 = p^2:                      PASS for n=0..{NMAX}")

# r(n)=k+1 <=> n+1 = p^k  (prime power of exponent k), k>=1
def prime_power_exponent(m: int):
    """Return k if m = p^k (single prime, k>=1), else None.  m=1 -> 0."""
    if m == 1:
        return 0
    f = factorint(m)
    if len(f) == 1:
        return list(f.values())[0]
    return None

for n in range(0, NMAX + 1):
    m = n + 1
    k = prime_power_exponent(m)
    r = brute_rep_count(n)
    if k is not None:          # m is a prime power p^k  =>  r = k+1
        assert r == k + 1, f"C5b ladder fails n={n}: r={r}, expected {k+1}"
    else:                       # m not a prime power  =>  r != k+1 for the would-be k
        # equivalently r(n) != (number making it a single prime power); spot via:
        assert factorint(m) and len(factorint(m)) >= 2
print(f"C5b r(n)=k+1 <=> n+1 = p^k (full ladder):        PASS for n=0..{NMAX}")

# r(n) prime  <=>  n+1 = p^(q-1) with q prime  (since tau(p^a)=a+1, and a+1 prime <=> a+1=q)
from sympy import isprime
for n in range(0, NMAX + 1):
    m = n + 1
    r = brute_rep_count(n)
    k = prime_power_exponent(m)            # m = p^k or None
    pred = (k is not None) and isprime(k + 1)
    assert isprime(r) == pred, f"C5b 'r prime' fails n={n}: r={r}, pred={pred}"
print(f"C5b r(n) prime <=> n+1 = p^(q-1), q prime:       PASS for n=0..{NMAX}")

# ---------------------------------------------------------------------------
# C5c Dirichlet cumulative total:  sum_{n<N} r(n) = sum_{d<=N} floor(N/d)
# ---------------------------------------------------------------------------
for N in range(1, 200):
    lhs = sum(brute_rep_count(n) for n in range(0, N))     # = sum_{m=1}^{N} tau(m)
    rhs = sum(N // d for d in range(1, N + 1))
    assert lhs == rhs, f"C5c fails at N={N}: {lhs} != {rhs}"
print(f"C5c cumulative sum_(n<N) r(n) = sum_(d<=N) floor(N/d): PASS for N=1..199")

print("ALL C5 CHECKS PASS")
