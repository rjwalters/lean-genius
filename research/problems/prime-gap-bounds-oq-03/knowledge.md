# Knowledge Base: prime-gap-bounds-oq-03

## Problem Understanding

### Core Goal
Connect the exponential bound `p_n ≤ 2^(n+1)` (from `PrimeGapBounds`) to the Chebyshev
functions θ(x) and ψ(x). Specifically:

1. **theta connection**: Use `nth_prime_le_two_pow_succ` and the definition of
   `chebyshevTheta` in `ChebyshevBounds` to derive a lower bound θ(x) ≥ c·x from the
   exponential bound, or equivalently relate π(x) ≥ log₂(x) to θ(x).

2. **psi definition**: `chebyshevPsi` (ψ) is NOT yet defined in the codebase. OQ-03
   asks us to define ψ(n) = Σ_{p^k ≤ n} log p (von Mangoldt sum) and relate it to θ.

### Key Available Infrastructure

| Theorem/Def | File | Statement |
|-------------|------|-----------|
| `nth_prime_le_two_pow_succ` | `PrimeGapBounds` | `nth Nat.Prime n ≤ 2^(n+1)` |
| `nth_prime_le_two_pow` | `PrimeGapBounds` | `nth Nat.Prime (n-1) ≤ 2^n` for n ≥ 1 |
| `chebyshevTheta` | `ChebyshevBounds` | `θ(n) = Σ_{p ≤ n, p prime} log p` |
| `chebyshevTheta_le` | `ChebyshevBounds` | `θ(n) ≤ n * log 4` |
| `chebyshevTheta_doubling_ge` | `ChebyshevBounds` | `θ(2n) - θ(n) ≥ log(n+1)` |
| `primeCounting_ge_log` | `ChebyshevBounds` | `log₂(n) ≤ π(n)` for n ≥ 2 |
| `nth_prime_is_prime` | `PrimeGapBounds` | `Nat.Prime (nth Nat.Prime n)` |

### The Logical Bridge

From `nth_prime_le_two_pow_succ`: `p_n ≤ 2^(n+1)`, taking logs:
```
log(p_n) ≤ (n+1) * log 2
```
So `n ≥ log(p_n)/log(2) - 1`. Since n = π(p_n) - 1:
```
π(p_n) ≥ log(p_n) / log 2
```
This gives **π(x) ≥ log₂(x)** for x of the form p_n — recovers `primeCounting_ge_log`.

For the theta direction: θ(p_n) ≥ log(p_n) (just the contribution of p_n itself).
Combined with the bound: `θ(p_n) ≥ log(p_n) ≥ log(p_{π(x)})`.

### The ψ Function (Not Yet Defined)

`chebyshevPsi` (second Chebyshev function): ψ(n) = Σ_{p prime, k≥1, p^k ≤ n} log p

Equivalently via von Mangoldt: ψ(n) = Σ_{m=1}^n Λ(m) where Λ(m) = log p if m = p^k, else 0.

Key relationship: θ(n) ≤ ψ(n) ≤ θ(n) + √n * log n (approximately).

The main theorems to prove:
1. Define `chebyshevPsi : ℕ → ℝ`
2. Prove `chebyshevTheta n ≤ chebyshevPsi n` (psi dominates theta)
3. Prove `chebyshevPsi n ≤ C * chebyshevTheta (Real.sqrt n)` or similar

## Approach

### Phase 1: theta-prime_bound connection
Prove a theorem combining `PrimeGapBounds` and `ChebyshevBounds`:
```lean
theorem theta_ge_log_nth_prime (n : ℕ) (hn : 1 ≤ n) :
    Real.log n ≤ chebyshevTheta (nth Nat.Prime (n - 1)) := by
  -- p_{n-1} is prime, so log(p_{n-1}) contributes to theta(p_{n-1})
  -- and p_{n-1} ≤ 2^n, so log(p_{n-1}) ≤ n * log 2
  sorry
```

### Phase 2: Define chebyshevPsi
```lean
noncomputable def chebyshevPsi (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), if ∃ p : ℕ, Nat.Prime p ∧ ∃ j : ℕ, 1 ≤ j ∧ p^j = k
                               then Real.log (Nat.minFac k) else 0
```
(Or equivalently via `Nat.vonMangoldt` if it exists in Mathlib.)

### Phase 3: theta ≤ psi
```lean
theorem chebyshevTheta_le_psi (n : ℕ) : chebyshevTheta n ≤ chebyshevPsi n
```

## Mathlib Search Notes

- Check `Mathlib.NumberTheory.vonMangoldt` for Λ(n)
- Check `Mathlib.NumberTheory.Chebyshev` (may not exist)
- `Nat.minFac` is available for extracting prime factor
- `Nat.factorization` gives prime factorizations
- `Real.log_pow` for log(p^k) = k * log p

## Key Risk

The psi definition requires careful handling of prime powers. The cleaner path
may be to define psi via the von Mangoldt function if Mathlib has it, or to
build it from `Nat.factorization`.
