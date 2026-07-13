# Problem: Erdős #727: Factorial Divisibility — Complete `main_implies_egrs`

**Slug**: erdos-727-incomplete-01
**Created**: 2026-04-03
**Status**: Active
**Source**: gallery-gap

## Problem Statement

**Lean file**: `proofs/Proofs/Erdos727Problem.lean`

The sorry is in `main_implies_egrs`:
```lean
theorem main_implies_egrs (k n : ℕ) (h : divides_factorial k n) :
    egrs_divides k n := by
  -- ((n+k)!)^2 | (2n)! and (n+1)! | (n+k)! implies (n+k)!(n+1)! | (2n)!
  sorry
```

Where:
- `divides_factorial k n ↔ ((n+k)!)^2 ∣ (2n)!`
- `egrs_divides k n ↔ (n+k)! * (n+1)! ∣ (2n)!`

## Key Argument

Chain of divisibility (k ≥ 1):
1. `(n+1)! ∣ (n+k)!` — `Nat.factorial_dvd_factorial` since `n+1 ≤ n+k`
2. `(n+k)! * (n+1)! ∣ ((n+k)!)^2` — multiply both sides by `(n+k)!`
3. `((n+k)!)^2 ∣ (2n)!` — hypothesis `h`
4. Transitivity gives the result

## Suggested Approach

```lean
theorem main_implies_egrs (k n : ℕ) (h : divides_factorial k n) :
    egrs_divides k n := by
  unfold divides_factorial egrs_divides at *
  have h1 : (n + 1)! ∣ (n + k)! := Nat.factorial_dvd_factorial (by omega)
  have h2 : (n + k)! * (n + 1)! ∣ ((n + k)!) ^ 2 := by
    rw [sq]; exact Nat.mul_dvd_mul_left _ h1
  exact dvd_trans h2 h
```

## Mathlib Lemmas Needed
- `Nat.factorial_dvd_factorial : m ≤ n → m ! ∣ n !`
- `Nat.mul_dvd_mul_left` or `dvd_mul_of_dvd_right`
- `dvd_trans`

## Tractability: LOW
