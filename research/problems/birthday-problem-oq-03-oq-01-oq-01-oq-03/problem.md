# birthday-problem-oq-03-oq-01-oq-01-oq-03

**Selected**: 2026-04-05

## Problem Statement

Remove the two threshold axioms from `Proofs/BirthdayProblemOQ03OQ01OQ01.lean` by proving them computationally via `native_decide`:

```lean
axiom birthday_threshold_lower :
    2 * birthdayCount3 88 365 < 365 ^ 88

axiom birthday_threshold_upper :
    365 ^ 87 ≤ 2 * birthdayCount3 87 365
```

Both are exact integer comparisons on large but computable values. The 2-way birthday problem already uses `native_decide` for 146-digit integers; the 3-way case uses the O(n²) `R` recurrence (≈7744 evaluations for n=88, d=365).

## Key Files

- **Lean file**: `proofs/Proofs/BirthdayProblemOQ03OQ01OQ01.lean` (lines 212–222)
- **Gallery entry**: `src/data/proofs/birthday-problem-oq-03-oq-01-oq-01/meta.json`
- **Parent proof**: `proofs/Proofs/BirthdayProblem.lean` (2-way case, uses native_decide for 146-digit numbers)

## Core Definition

```lean
def R : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 1
  | n + 1, e, s => e * R n (e - 1) (s + 1) + s * R n e (s - 1)

def birthdayCount3 (n d : ℕ) : ℕ := R n d 0
```

## Approach

Replace each `axiom` with `theorem ... := by native_decide`.

**Risk**: The values for n=88, d=365 may exceed what Lean's elaborator can evaluate — but this is a compile-time native_decide, which uses GMP-backed big integers. The 2-way problem succeeded with 146-digit numbers. The recurrence has O(n²) = ~7744 steps.

**Fallback**: If `native_decide` times out, try `decide` (slower) or prove a reformulation using `Nat.decideEq` with an explicit precomputed value.

## Significance

Eliminating both axioms reduces `axiomCount` from 2 → 0, changing the badge from `axiom` → `verified`.
