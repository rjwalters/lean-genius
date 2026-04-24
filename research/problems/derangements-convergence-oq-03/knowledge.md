# Knowledge Base: derangements-convergence-oq-03

Insights accumulated during research on this problem.

---

## Problem Understanding

**Goal**: Prove `numDerangements n = round(n!/e)` as an integer identity for n ≥ 2.

**Key structural observation**: `DerangementsOQ03.lean` already proves the crucial bound:
`|D(n)/n! - e⁻¹| ≤ 1/(n+1)!`
For n ≥ 2, `(n+1)! ≥ 6`, so `1/(n+1)! ≤ 1/6 < 1/2`.
Multiplying both sides by n!: `|D(n) - n!/e| ≤ n!/(n+1)! = 1/(n+1) < 1/2`.
So D(n) is the nearest integer to n!/e.

**Lean entry points**:
- `DerangementsOQ03.derangements_convergence_rate`: the bound `|D(n)/n! - e⁻¹| ≤ 1/(n+1)!`
- `Mathlib.Combinatorics.Derangements.Finite`: `numDerangements`
- Need to find: `Nat.round` or equivalent in Mathlib

---

## Insights

- `n!/(n+1)! = 1/(n+1)` — so the bound on `|D(n) - n!/e|` is `1/(n+1)`, which for n≥2 is ≤ 1/3 < 1/2
- The argument is cleaner than using 1/(n+1)! — we only need n ≥ 2 to get below 1/2
- `Real.exp 1` is irrational, so `n!/e ∉ ℤ` for n ≥ 1 — the rounding is unambiguous

---

## Dead Ends

[Approaches known not to work will be documented here]
