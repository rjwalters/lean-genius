# sum-of-divisors-oq-01 — Euler's prime-factor constraint on odd perfect numbers

## Status

S1 ORIENT (researcher-4, 2026-06-14). Build-free orientation under
dual-backend blackout (Docker down; Aristotle returns "Resource not found").
No Lean file produced yet; deliverable is the precise problem statement, a
bearer audit, a proof plan, and a reproducible numerical certificate.

## The question (made precise)

The seeker stub gives only the title *"Euler's prime-factor constraint on
odd perfect numbers."* The intended target is **Euler's structural theorem
(1747)**, a fully provable statement — distinct from the open *existence*
question (whether any odd perfect number exists at all).

**Theorem (Euler).** If `N` is odd and perfect (`σ(N) = 2N`), then
```
        N = p^a · m²
```
with `p` prime, `p ≡ 1 (mod 4)`, `a ≡ 1 (mod 4)`, and `gcd(p, m) = 1`
(equivalently `p ∤ m`). The prime `p` is the **special** (or **Euler**)
prime; every other prime divides `N` to an even power.

This is the natural OQ-01 for the `sum-of-divisors` gallery entry: that
entry and its siblings formalize **even** perfect numbers (Euclid–Euler,
`SumOfDivisorsOQ02.lean`) and Mersenne-prime distribution
(`PerfectNumbersOQ03.lean`); the **odd** case is uncovered.

## Why it is tractable (and what is NOT being claimed)

- The conclusion does **not** require any odd perfect number to exist. It is
  a conditional ("if N is odd and perfect, then …"), provable outright.
- The **existence** of odd perfect numbers stays OPEN and is explicitly out
  of scope. Do not conflate the two.

## Key reduction (orientation insight)

The structural conclusion follows already from
```
        N odd  and  v₂(σ(N)) = 1
```
because `σ(N) = 2N` with `N` odd gives `v₂(σ(N)) = v₂(2N) = 1`. So the
theorem is a corollary of the cleaner

**Euler-form lemma.** For every odd `N > 1` with `v₂(σ(N)) = 1`,
`N = p^a · m²` with `p` prime, `p ≡ a ≡ 1 (mod 4)`, `gcd(p, m) = 1`.

This reframing matters twice: (i) it is what makes the result **numerically
testable on ~10⁵ genuine witnesses** rather than the empty set of odd
perfect numbers; (ii) it cleanly separates the "perfect" arithmetic
(`σ(N) = 2N ⇒ v₂ = 1`) from the multiplicative structure theory.

## Proof skeleton (classical; Euler 1747 / e.g. Hardy–Wright Thm 277)

Write `N = ∏ pᵢ^{aᵢ}` (all `pᵢ` odd). `σ` is multiplicative, so
`σ(N) = ∏ σ(pᵢ^{aᵢ})`.

1. **Parity of σ(p^a).** For odd `p`, `σ(p^a) = 1 + p + ⋯ + p^a` is a sum of
   `a+1` odd terms, so `σ(p^a) ≡ a+1 (mod 2)`; hence `σ(p^a)` is odd ⟺ `a`
   is even. *(Lemma L1.)*
2. **Exactly one odd exponent.** `v₂(σ(N)) = Σᵢ v₂(σ(pᵢ^{aᵢ})) = 1`. Each
   summand is `≥ 1` exactly when `σ(pᵢ^{aᵢ})` is even, i.e. (by L1) when
   `aᵢ` is odd. The total being `1` forces exactly one index `i = i₀` with
   `a_{i₀}` odd (and that summand contributes `v₂ = 1`); all other `aᵢ` even.
   Let `p = p_{i₀}`, `a = a_{i₀}`; the remaining part is a perfect square
   `m²` coprime to `p`.
3. **Mod-4 refinement on the special prime.** With `a` odd and
   `v₂(σ(p^a)) = 1`: pairing terms `σ(p^a) = (1+p)(1 + p² + ⋯ + p^{a-1})`
   shows `v₂(σ(p^a)) = 1 ⟺ p ≡ 1 (mod 4)` **and** `a ≡ 1 (mod 4)`. *(Lemma
   L2.)* This pins `p ≡ a ≡ 1 (mod 4)`.

Combining (2)+(3): `N = p^a · m²` with `p ≡ a ≡ 1 (mod 4)`, `p ∤ m`. ∎

## Numerical certificate

`verify_euler_oddperfect.py` (sympy only) confirms, reproducibly:

- **L1** PASS over odd primes `p ≤ 101`, exponents `a ≤ 11`.
- **L2** PASS over odd primes `p ≤ 113`, odd exponents `a ≤ 39` (140
  positive witnesses of `v₂ = 1`).
- **Euler-form lemma**: over all odd `N ∈ [3, 2·10⁶)` with `v₂(σ(N)) = 1`,
  **98 653 witnesses checked, 0 failures** — each is `p^a·m²` with
  `p ≡ a ≡ 1 (mod 4)`, `p ∤ m`.
- **Sanity**: no odd perfect number below `2·10⁶` (consistent with the
  existence question being open; the structural theorem is verified on the
  non-perfect witnesses above, not on perfect ones).

## Out of scope

- Existence/non-existence of odd perfect numbers (open).
- Sharper constraints (Ochem–Rao bounds, ≥ 10 distinct prime factors,
  N > 10^1500, etc.) — separate, much harder targets.
