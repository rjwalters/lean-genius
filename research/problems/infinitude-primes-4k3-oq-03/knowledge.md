# Knowledge Base: infinitude-primes-4k3-oq-03

Insights accumulated during research on this problem.

---

## Problem Understanding

- Goal: elementary proof that infinitely many primes p ≡ 1 (mod 4)
- Key construction: N = (2·p₁·...·pₖ)² + 1, which must have a prime factor ≡ 1 mod 4
- Requires: if q | a²+1 then q ≡ 1 mod 4 (key number theory lemma via element order)

---

## Insights

- Key lemma: if prime q | a²+1, then q ≡ 1 mod 4
  - a² ≡ -1 (mod q) → a⁴ ≡ 1 (mod q) → ord_q(a) ∈ {1,2,4}
  - Not 1: a ≢ 1 (mod q) since a²≡-1≢0
  - Not 2: a²≡-1≢1 (mod q) for odd q
  - So ord_q(a) = 4, and ord_q(a) | q-1, so 4 | q-1, q ≡ 1 mod 4 ✓

- Lean approach:
  - `ZMod.orderOf_dvd_card_sub_one`: order of element divides p-1 in ZMod p
  - `orderOf_dvd_of_pow_eq_one`: ord(a) | n if a^n = 1
  - Coprimality: gcd((2P)²+1, 2P) = gcd(1, 2P) = 1, so new prime factor exists

---

## Dead Ends

- None identified; argument is classical and elementary
