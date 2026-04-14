# Erdős #35: Schnirelmann Density and Additive Bases

**Problem**: If B ⊆ ℕ is an additive basis of order k with 0 ∈ B, prove d_s(A + B) ≥ α + α(1-α)/k where α = d_s(A).
**Status**: SOLVED (Plünnecke 1970); formalized in Lean with 4 sorries remaining (3 HARD + 1 OPEN).
**File**: `proofs/Proofs/Erdos35Problem.lean` (5→4 sorries), `proofs/Proofs/Erdos35ProblemAristotle.lean` (2→1 sorries)

---

## Session 2026-04-13 (Session 1) — Initial Formalization + Lagrange Proof

**Mode**: FRESH
**Outcome**: progress (2 sorries eliminated)

### What I Did
- Claimed erdos-35 lock (stale lock from dead process 28246 removed first)
- Read `Erdos35Problem.lean` (5 sorries) and `Erdos35ProblemAristotle.lean` (2 sorries)
- Identified `squares_basis_order_4` as provable via `Nat.sum_four_squares`
- Identified `rpow_ge_self_of_le_one` as provable via `Real.rpow_le_rpow_of_exponent_ge`
- Added `import Mathlib.NumberTheory.SumFourSquares`
- Proved `squares_basis_order_4` using Lagrange four-square theorem
- Proved `rpow_ge_self_of_le_one` via exponent monotonicity on [0,1]

### Key Findings
- `Nat.sum_four_squares n` gives `∃ a b c d, a^2 + b^2 + c^2 + d^2 = n` directly
- `kFoldSum squares 4` nested sumset structure matches perfectly: level by level witnesses
- `Real.rpow_le_rpow_of_exponent_ge : 0 < b → b ≤ 1 → e₂ ≤ e₁ → b^e₁ ≤ b^e₂` — decreasing exponent increases value for base ≤ 1
- Case split on `α = 0` needed: `Real.rpow_nonneg` handles `0^r ≥ 0`; positive α uses the monotonicity lemma
- 3 HARD sorries remain: `erdos_1936_bound`, `plunnecke_inequality`, `power_bound_implies_erdos` — all deep analytic results
- 1 OPEN sorry: `primes_basis_conditional` requires Goldbach conjecture

### Files Modified
- `proofs/Proofs/Erdos35Problem.lean`: added import, proved `squares_basis_order_4`
- `proofs/Proofs/Erdos35ProblemAristotle.lean`: proved `rpow_ge_self_of_le_one`

### Next Steps
- Submit `erdos_1936_bound` and `power_bound_implies_erdos` to Aristotle (HARD calculus/analytic)
- `plunnecke_inequality` is blocked — Plünnecke's theorem needs substantial infrastructure
- Mark `primes_basis_conditional` as OPEN (depends on Goldbach)
- Commit and push to feature branch, create PR
