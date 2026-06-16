# Problem: abundant-number-oq-01

**Slug**: abundant-number-oq-01
**Status**: Active (ACT, build-gated)
**Source**: seeker-selected
**Tier**: C · significance 4 · tractability 8

## Problem Statement

### Formal Statement

12 is the least abundant number: `IsLeast {n : ℕ | n.Abundant} 12`. Equivalently,
`Nat.Abundant 12` holds and no `0 ≤ n < 12` is abundant, where `n` is abundant
iff `n < ∑ d ∈ n.properDivisors, d`.

### Plain Language

An abundant number is one whose proper divisors sum to more than the number
itself. 12 (proper divisors 1+2+3+4+6 = 16 > 12) is the smallest such number;
everything below it is deficient or perfect (6 is perfect: 1+2+3 = 6).

### Why This Matters

Canonical recreational-number-theory landmark. Mathlib defines `Nat.Abundant`
and proves `Nat.abundant_twelve`, but does **not** prove minimality. This entry
supplies the missing "smallest" claim — a clean, axiom-free, fully decidable
target.

## Known Results

### What's Already Proven (Mathlib)

- `Nat.Abundant`, `Nat.Deficient`, `Nat.Perfect` definitions
  (`Mathlib/NumberTheory/FactorisationProperties.lean`).
- `Nat.abundant_twelve : Nat.Abundant 12`.

### What This Entry Adds

- `not_abundant_below_twelve : ∀ n < 12, ¬ Nat.Abundant n` (by `decide`).
- `smallest_abundant : IsLeast {n : ℕ | n.Abundant} 12`.

### What's Still Open (this entry)

- Compile `proofs/Proofs/AbundantNumberOQ01.lean` once a build slot is available
  (Docker pool + Aristotle backend both unavailable this session).
- Register in `Proofs.lean` and add gallery data after a green build.
