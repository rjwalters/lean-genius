# Problem: Connect Exponential Bound to Chebyshev theta(x) and psi(x)

## Statement

### Plain Language
Formalize the connection between the exponential bound `p_n ≤ 2^(n+1)` (from
`PrimeGapBounds`) and the Chebyshev functions θ(x) and ψ(x) (from `ChebyshevBounds`).
This involves:
1. Deriving a lower bound on θ(x) implied by the prime exponential bound
2. Defining the second Chebyshev function ψ(x) = Σ_{p^k ≤ x} log p
3. Proving θ(x) ≤ ψ(x) and relating both to the exponential prime bound

### Formal Statement
```lean
-- Target theorem bridging the two files:
theorem theta_lower_from_exp_bound (n : ℕ) (hn : 1 ≤ n) :
    Real.log ↑n / Real.log 2 ≤ ChebyshevBounds.chebyshevTheta (2^n)

-- Definition to add:
noncomputable def chebyshevPsi (n : ℕ) : ℝ :=
  -- sum of log p over all prime powers p^k ≤ n

-- Key relationship:
theorem chebyshevTheta_le_psi (n : ℕ) :
    ChebyshevBounds.chebyshevTheta n ≤ chebyshevPsi n
```

## Classification

```yaml
tier: B
significance: 7
tractability: 7
tags:
  - number-theory
  - primes
  - chebyshev
  - analytic
  - seeker-selected
```

**Significance**: 7/10 — Bridges two verified gallery proofs; ψ definition is
infrastructure toward the Prime Number Theorem.

**Tractability**: 7/10 — The theta lower bound follows directly from
`nth_prime_le_two_pow_succ` + `primeCounting_ge_log`. The ψ definition requires
careful prime-power enumeration but Mathlib has the tools.

## Why This Matters

1. **Bridge proof**: Connects `PrimeGapBounds.lean` and `ChebyshevBounds.lean` into a
   coherent framework for analytic number theory.
2. **PNT infrastructure**: ψ(x) ~ x is equivalent to the Prime Number Theorem; defining
   ψ formally is a prerequisite for any PNT formalization.
3. **Classical result**: The equivalence θ ≤ ψ and ψ ~ θ (up to O(√x log x)) is a
   standard result in every analytic number theory textbook.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `prime-gap-bounds` | Source of `nth_prime_le_two_pow_succ` (p_n ≤ 2^(n+1)) |
| `chebyshev-bounds` | Source of `chebyshevTheta`, `primeCounting_ge_log` |
| `bounded-prime-gaps` | Uses similar prime counting infrastructure |
| `prime-number-theorem-oq-03` | Downstream: PNT formalization depends on ψ |
