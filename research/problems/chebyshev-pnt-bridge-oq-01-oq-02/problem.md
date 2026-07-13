# Problem: Chebyshev Prime Bound via Nat.factorization_prod_pow_eq_self

**Slug**: chebyshev-pnt-bridge-oq-01-oq-02
**Created**: 2026-04-21
**Status**: Active
**Source**: gallery-extension

## Problem Statement

### Plain Language

The gallery proof `ChebyshevPNTBridge.lean` establishes the product bound
`central_binom_le_pow_prime_counting` showing `(central binomial coefficient) ≤ 4^n`
via prime factorization. The parent open question (`chebyshev-pnt-bridge-oq-01`) asked
about using `Nat.factorization_prod_pow_eq_self` to reconstruct the central binomial
from its prime factorization. This sub-question asks:

**Can the product bound `central_binom_le_pow_prime_counting` be proved using
`Nat.factorization_prod_pow_eq_self` to reconstruct the central binomial coefficient
from its prime factorization, rather than via the existing inequality chain?**

The key idea is to express `C(2n, n)` as `∏ p^(v_p(C(2n,n)))` over primes p ≤ 2n,
then bound each `p^(v_p(C(2n,n)))` by `p^(log_p(2n)) ≤ 2n`, yielding the product
bound more directly. The Kummer theorem connection is also relevant: `v_p(C(m+n, n))`
equals the number of carries when adding m and n in base p.

### Formal Context

The parent proof (`ChebyshevPNTBridge.lean`) contains:
- `theorem chebyshev_upper : (n.primeCounting : ℝ) * Real.log 2 ≤ Real.log n`
- Product bounds connecting central binomial coefficients to prime counting

The relevant Mathlib lemma:
```lean
theorem Nat.factorization_prod_pow_eq_self {n : ℕ} (hn : n ≠ 0) :
    n.factorization.prod (· ^ ·) = n
```

### Why This Matters

- Provides a cleaner, more conceptual proof of the central Chebyshev bound
- Demonstrates the power of `Nat.factorization` in analytic number theory
- Connects Kummer's theorem on carries to the prime counting bound
- Would enrich the `chebyshev-pnt-bridge` gallery entry with an alternative proof path

## Known Results

### From Parent Proof

The `ChebyshevPNTBridge.lean` proof already establishes:
- `central_binom_le_pow_prime_counting`: The central binomial bound
- The connection between `Nat.choose 2n n` and products over primes ≤ 2n

### Mathlib Support

- `Nat.factorization_prod_pow_eq_self`: Reconstruct n from prime factorization
- `Nat.factorization_choose`: `(n.choose k).factorization p = ...` — exists in Mathlib
- `Nat.ord_compl_dvd`: Divisibility from factorization
- `Finsupp.prod_filter_index`: For filtering the prime product

## Suggested Approach

### Phase 1: OBSERVE
1. Read `ChebyshevPNTBridge.lean` to find the current proof of `central_binom_le_pow_prime_counting`
2. Check Mathlib for `Nat.factorization_choose` and `Nat.factorization_centralBinom`
3. Look for `Nat.centralBinom_factorization` or similar

### Phase 2: ORIENT
1. Survey existing Mathlib lemmas about factorization and binomial coefficients
2. Check if `Kummer.factorization` or `Nat.add_factorization` tools exist
3. Assess whether `Nat.factorization_prod_pow_eq_self` route is shorter than current proof

### Phase 3: DECIDE
1. If the factorization approach is strictly cleaner, sketch the proof
2. If the existing approach is already optimal, document why and close

### Phase 4: ACT
The proof structure would be:
```lean
-- Bound: C(2n, n) = ∏ p^(v_p(C(2n,n))) for p prime ≤ 2n
-- Each p^(v_p(C(2n,n))) ≤ 2n (since p^(v_p(C(2n,n))) ≤ p^(log_p(2n)) ≤ 2n)
-- Number of primes ≤ 2n is π(2n)
-- Therefore: C(2n, n) ≤ (2n)^(π(2n))
```

## Related Gallery Proofs

- `chebyshev-pnt-bridge`: Parent proof (verified, 0 sorries) — the main context
- `chebyshev-bounds`: Related Chebyshev θ/ψ function bounds
- `basel-problem`: Uses similar factorization-based arguments

## Quality Assessment

- **Tractability**: 7/10 — specific approach suggested, good Mathlib support
- **Significance**: 7/10 — improves proof elegance for a key result
- **Domain**: Number theory / analytic number theory
- **Risk**: Low — if the approach doesn't work, the existing proof still stands
