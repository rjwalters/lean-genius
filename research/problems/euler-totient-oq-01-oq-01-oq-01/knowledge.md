# Knowledge Base: euler-totient-oq-01-oq-01-oq-01

Insights accumulated during research on this problem.

---

## Problem Understanding

The parent (`euler-totient-oq-01-oq-01`) proves the keystone λ(m·n)=lcm(λ(m),λ(n))
for coprime m, n and asks to complete the induction to λ(n)=lcm_i λ(pᵢ^kᵢ).

**Dedup finding:** that literal identity — and *all three* of the parent's stated
open questions — are already in Mathlib's
`Mathlib/NumberTheory/ArithmeticFunction/Carmichael.lean`:
- `carmichael_factorization` : λ(n) = lcm over primeFactors of λ(p^{k_p})
- `carmichael_pow_of_prime_ne_two` : λ(p^k) = φ(p^k) for odd p
- `carmichael_two_pow_of_ne_two` : λ(2^k) = 2^{k-2} for k ≠ 2
- plus `carmichael_mul`/`carmichael_lcm`, `pow_carmichael`, `carmichael_dvd_totient`.

The parent file even reproved `carmichael_mul` locally. So a faithful re-proof
of the open question is a thin wrapper. The honest contribution is the
**explicit assembled closed form** and **concrete data** Mathlib does not state.

---

## Insights

- For **odd n**, every prime factor is odd, so each factor λ(p^k)=φ(p^k)=p^{k-1}(p-1)
  is a clean cyclic-group order; the prime 2 is the only obstruction to a single
  power formula (non-cyclic units for k≥3), which is why the explicit statement is
  cleanest restricted to odd n.
- Engine for `carmichael_odd_eq_lcm_explicit`: `rw [carmichael_factorization n]`
  then `Finset.lcm_congr rfl`; per factor use `prime_of_mem_primeFactors`,
  `dvd_of_mem_primeFactors`, `Nat.Prime.factorization_pos_of_dvd`, and
  `p ≠ 2` from `Odd n` (else `2 ∣ n` via `even_iff_two_dvd`,
  contradicting `Nat.not_even_iff_odd.mpr hodd`).
- Concrete Carmichael values are computable despite `Carmichael` being
  noncomputable: iterate `carmichael_mul` over coprime prime factors down to
  λ(p)=p−1, then `decide` the small nested `Nat.lcm`. `carmichael_mul` needs the
  `Coprime` side-goals by `decide`.
- λ(561)=lcm(2,10,16)=80 ∣ 560 is the Korselt witness making 561 the first
  Carmichael number.

---

## Dead Ends

- Reproving `carmichael_factorization` / `carmichael_mul` from scratch — pointless,
  Mathlib already has them. Always grep
  `.lake/packages/mathlib/Mathlib/NumberTheory/ArithmeticFunction/Carmichael.lean`
  before formalizing a named Carmichael identity.
- A single clean closed form valid for all n (including the 2-part) — blocked by
  the piecewise λ(2^k); deferred to a follow-up.
