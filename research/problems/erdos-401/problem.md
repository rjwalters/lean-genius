# Problem: Erdős #401: Factorial Divisibility with Prime Products

## Statement

### Plain Language
Erdős asked: does there exist a function f(r) → ∞ as r → ∞ such that for infinitely
many n, there exist a₁, a₂ with a₁ + a₂ > n + f(r)·log(n), where
a₁! · a₂! divides n! · 2ⁿ · 3ⁿ · … · pᵣⁿ?

**Answer: YES.** Proved by Barreto-Leeham (2026) using the same construction as
Erdős #729. The "for all large n" version is FALSE (Sothanaphan counterexample).

### Formal Statement
```
Erdos401Conjecture : ∃ f : ℕ → ℝ, Tendsto f atTop atTop ∧
  ∀ r : ℕ, ∃ᶠ n in atTop, ∃ a₁ a₂ : ℕ,
    FactorialDivides a₁ a₂ n r ∧ n + f r * Real.log n < a₁ + a₂
```

where `FactorialDivides a₁ a₂ n r` means `a₁! · a₂! ∣ n! · ∏_{p ≤ pᵣ} pⁿ`.

## Classification

```yaml
tier: B
significance: 6
tractability: 7
tags:
  - seeker-selected
  - erdos
  - axiom-reduction
  - number-theory
  - factorials
  - divisibility
  - primes
```

**Significance**: 6/10
**Tractability**: 7/10

## Current Lean Status

File: `proofs/Proofs/Erdos401Problem.lean`

**3 axioms remaining:**

1. `erdos_graham_baseline` — Erdős-Graham upper bound: if a₁!·a₂! ∣ n!, then
   a₁ + a₂ ≤ n + C·log n for some constant C > 0. (Combinatorial number theory, 1980)

2. `barreto_leeham_401` — The main conjecture is true: ∃ f(r) → ∞ such that for
   infinitely many n, the divisibility with prime powers allows a₁ + a₂ > n + f(r)·log n.

3. `sothanaphan_counterexample` — The "for all large n" strong version is false:
   ¬Erdos401Strong, using n = p_{r+1}^k - 1.

## Why This Matters

1. **Axiom reduction target**: 3 axioms provide a concrete tractable goal. The
   `erdos_graham_baseline` is a classical result that may be formalizable from
   Mathlib's `Nat.factorial` and multiplicity tools.

2. **Sothanaphan counterexample**: The construction n = p_{r+1}^k - 1 is explicit
   and may be directly formalizable — check if Mathlib has `Nat.nth_prime` or
   Legendre's formula for `p-adic` valuations of factorials.

3. **Connection to #729**: The comment notes Barreto-Leeham use the same technique
   as Erdős #729. Survey whether Erdos729 already has relevant infrastructure.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| erdos-401 | Main gallery proof (parent, axiomatized, 3 axioms) |
| erdos-729 | Same Barreto-Leeham construction technique; check for reusable lemmas |
| bertrands-postulate | Prime distribution tools (Bertrand's postulate in Mathlib) |

## Research Focus

**Primary goal**: Reduce axiom count from 3 to 2 or fewer.

**Best target**: `sothanaphan_counterexample` — the explicit construction
n = p_{r+1}^k - 1 is concrete. Check:
- Mathlib `Nat.factorial_prime_pow` or similar
- `Nat.ord_compl_dvd` / `Nat.factorization` for p-adic valuations
- Whether `n = pᵏ - 1` makes the bound tight via Kummer's theorem

**Secondary**: `erdos_graham_baseline` — classical Erdős-Graham result. Look for:
- `Nat.factorial_dvd_factorial` and divisibility chains in Mathlib
- Legendre's formula: `v_p(n!) = Σ ⌊n/pⁱ⌋` (may be in `Mathlib.Data.Nat.Multiplicity`)
