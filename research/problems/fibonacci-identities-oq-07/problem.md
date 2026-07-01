# Problem: Fibonacci Divisibility Characterization F_m ∣ F_n ⟺ m ∣ n

**Slug**: fibonacci-identities-oq-07
**Created**: 2026-07-01
**Status**: Active
**Source**: proof-suggestion <!-- gallery open-question spawned from verified parent -->
**Parent**: fibonacci-identities

## Problem Statement

### Formal Statement

$$
\text{For } m \ge 3:\qquad F_m \mid F_n \iff m \mid n.
$$

with the corollary that if $F_n$ is prime then $n = 4$ or $n$ is prime.

### Plain Language

Mathlib proves the *forward* divisibility `Nat.fib_dvd : m ∣ n → fib m ∣ fib n`, and the
beautiful gcd identity `Nat.fib_gcd : fib (gcd m n) = gcd (fib m) (fib n)`. It does **not**
package the *converse*, so it lacks the full **biconditional** `F_m ∣ F_n ⟺ m ∣ n`. This
child supplies the converse and assembles the clean iff (for indices `m ≥ 3`, which avoids
the degenerate `F_1 = F_2 = 1`), then derives the classic corollary that Fibonacci primes
sit at prime indices (or the exceptional index `4`, where `F_4 = 3`).

### Why This Matters

The converse is the mathematically interesting half — it says Fibonacci divisibility *sees*
index divisibility exactly. The proof is a short, elegant reduction through `fib_gcd`:
`F_m ∣ F_n ⟹ gcd(F_m, F_n) = F_m ⟹ F_{gcd(m,n)} = F_m ⟹ gcd(m,n) = m` (using strict
monotonicity of `fib` on `[2,∞)`), i.e. `m ∣ n`. It showcases how a single gcd identity
plus monotonicity yields a divisibility characterization.

## Known Results

### What's Already Proven

- Parent `fibonacci-identities` is verified (0-axiom).
- Mathlib: `Nat.fib_gcd (m n) : fib (gcd m n) = gcd (fib m) (fib n)`,
  `Nat.fib_dvd (m n) (h : m ∣ n) : fib m ∣ fib n`,
  `Nat.fib_strictMonoOn : StrictMonoOn fib (Set.Ici 2)`,
  `Nat.fib_lt_fib (hm : 2 ≤ m) : fib m < fib n ↔ m < n`,
  `Nat.fib_coprime_fib_succ`.

### What's Still Open

- The biconditional and its corollary below (currently `sorry`). Mathlib has only the
  forward direction `Nat.fib_dvd`.

### Our Goal

Prove the sketch below as a self-contained verified (0-axiom) child. Category:
**characterization / completion**.

## Target Lean Sketch

```lean
open Nat

/-- Fibonacci divisibility mirrors index divisibility (for indices `≥ 3`). -/
theorem fib_dvd_iff {m n : ℕ} (hm : 3 ≤ m) : fib m ∣ fib n ↔ m ∣ n := by
  constructor
  · intro h
    -- fib m ∣ fib n  ⟹  gcd (fib m) (fib n) = fib m
    -- rewrite with `Nat.fib_gcd`:  fib (gcd m n) = fib m
    -- gcd m n ∣ m and (m ≥ 3) so both indices are in `Set.Ici 2`;
    -- `fib_strictMonoOn` injectivity forces gcd m n = m, i.e. m ∣ n.
    sorry
  · intro h
    exact fib_dvd m n h

/-- Fibonacci primes occur at index 4 or at prime indices. -/
theorem index_prime_of_fib_prime {n : ℕ} (hn : (fib n).Prime) : n = 4 ∨ n.Prime := by
  sorry
  -- If n is composite with a proper divisor d (2 ≤ d < n), then fib d ∣ fib n with
  -- 1 < fib d < fib n, contradicting primality — except the boundary case n = 4.
```

Add worked `example`s: `F_6 = 8`, `F_3 = 2 ∣ 8` and `3 ∣ 6`; `F_5 = 5` prime, `5` prime;
`F_4 = 3` prime, index `4` composite (the lone exception); `F_7 = 13` prime, `7` prime.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `fibonacci-identities` | Parent: Fibonacci identities | recurrences, induction |
| `fibonacci-identities-oq-02` | Sibling: divisibility/gcd threads | number theory |
| `gcd-algorithm` | gcd machinery underlying `fib_gcd` | Euclidean algorithm |

## Tractability Assessment

**Difficulty**: Low-Medium

**Significance**: 6/10  |  **Tractability**: 8/10  |  **Tier**: B

**Justification**: The converse is a three-line chain: `dvd → gcd_eq → fib_gcd rewrite →
monotone injectivity`. The only care needed is the small-index boundary (`m ≥ 3`) and the
`n = 4` exception in the corollary. All primitives (`fib_gcd`, `fib_strictMonoOn`,
`fib_dvd`) are in Mathlib.

### Suggested First Steps

1. Prove the converse: from `fib m ∣ fib n` get `Nat.gcd (fib m) (fib n) = fib m`
   (`Nat.gcd_eq_left`), rewrite via `Nat.fib_gcd`, then apply injectivity of
   `fib_strictMonoOn` on `Set.Ici 2` to conclude `gcd m n = m`.
2. Combine with `Nat.fib_dvd` for the reverse to close `fib_dvd_iff`.
3. Derive `index_prime_of_fib_prime` by contradiction on a proper divisor of `n`, handling
   `n = 4` separately; add `decide` worked examples.

## References

### Mathlib

- `Nat.fib_gcd` — Data/Nat/Fib/Basic.lean
- `Nat.fib_dvd` — Data/Nat/Fib/Basic.lean
- `Nat.fib_strictMonoOn`, `Nat.fib_lt_fib` — Data/Nat/Fib/Basic.lean

### Literature

- The identity `gcd(F_m, F_n) = F_{gcd(m,n)}` and its divisibility corollary are classical
  (Lucas). The Fibonacci-prime index result is a standard consequence.

## Metadata

```yaml
tags:
  - number-theory
  - fibonacci
  - divisibility
  - integer-sequences
related_proofs:
  - fibonacci-identities
  - gcd-algorithm
difficulty: low
source: proof-suggestion
created: 2026-07-01
```
