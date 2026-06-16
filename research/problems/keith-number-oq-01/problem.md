# Problem: keith-number-oq-01

**Slug**: keith-number-oq-01
**Status**: Active (ACT, build-gated)
**Source**: seeker-selected
**Tier**: C · significance 4 · tractability 7

## Problem Statement

### Formal Statement

14 is the least Keith number: `IsLeast {n : ℕ | IsKeith n} 14`, where `IsKeith n`
holds iff `10 ≤ n` and the digit recurrence of `n` reaches `n`. The recurrence
starts from the decimal digits of `n` (most-significant first) and, at each step,
appends the sum of the current length-`d` window (`d` = number of digits) while
dropping the oldest term.

### Plain Language

A Keith number (or repfigit, "repetitive Fibonacci-like digit") is an `n`-digit
number `≥ 10` that appears in the integer sequence generated from its own digits,
where each new term is the sum of the previous `n` terms. For 14: the digits
`1, 4` generate `1, 4, 5, 9, 14`, and 14 itself shows up — so 14 is Keith. The
two-digit numbers below it (10, 11, 12, 13) all overshoot without landing on
themselves, and single-digit numbers are excluded by definition. Hence 14 is the
smallest Keith number (OEIS A007629 begins 14, 19, 28, 47, …).

### Why This Matters

Canonical recreational-number-theory landmark. The Keith recurrence is a
digit-driven linear recurrence; minimality is a clean finite computation. Mathlib
has no notion of Keith numbers, so this entry both defines the predicate and
proves the smallest-element claim — a self-contained, axiom-free, fully decidable
target.

## Known Results

### What's Already Proven (Mathlib)

- Nothing specific to Keith numbers; Mathlib has no `Keith`/repfigit predicate.
- Standard infrastructure only: `Nat` division/mod, `List.sum`, `IsLeast`,
  `Nat.decidableBallLT`.

### What This Entry Adds

- `IsKeith : ℕ → Prop` plus a `DecidablePred` instance built from a fuel-bounded,
  structurally-recursive digit recurrence (`lsdDigits`, `step`, `reaches`).
- `keith_fourteen : IsKeith 14`.
- `not_keith_below_fourteen : ∀ n < 14, ¬ IsKeith n` (by `decide`).
- `smallest_keith : IsLeast {n : ℕ | IsKeith n} 14`.

### What's Still Open (this entry)

- Compile `proofs/Proofs/KeithNumberOQ01.lean` once a build slot is available
  (Docker pool unavailable this session).
- Register in `Proofs.lean` and add gallery data after a green build.

### Design Note

The recurrence uses a custom `lsdDigits` (structural recursion on fuel) rather
than Mathlib's `Nat.digits`, which is defined by well-founded recursion and does
not reliably reduce under kernel `decide`. With the custom function the whole
result is axiom-free (no `native_decide`/`Lean.ofReduceBool`).
