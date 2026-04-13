# Knowledge Base: combinations-formula-oq-02

Insights accumulated during research on Catalan numbers and the convolution identity.

---

## Problem Understanding

**Problem**: Formalize Catalan number properties in Lean 4:
- Definition via ballot formula: C_n = C(2n,n) - C(2n,n+1)
- Fundamental identity: C_n * (n+1) = C(2n,n)
- Convolution: C_{n+1} = ∑_{k=0}^{n} C_k * C_{n-k}
- Bounds: C_n ≤ 4^n, C(2n,n) ≥ 2^n

Our definition avoids division (stays in ℕ): `catalan n = C(2n,n) - C(2n,n+1)`.

---

## Session 2026-04-13 (Session 2) — Complete: 0 Sorries

**Mode**: REVISIT
**Outcome**: completed — catalan_convolution proved, PR #10487 created

### What I Did
- Proved `catalan_convolution` by bridging to Mathlib's recursive `_root_.catalan`
- Added `import Mathlib.Combinatorics.Enumerative.Catalan`

### Key Technique: Mathlib Bridge
The key insight is that our ballot-formula catalan equals Mathlib's recursive catalan:
1. Our `catalan_mul_succ`: `catalan m * (m+1) = Nat.choose (2*m) m`
2. Mathlib's `catalan_eq_centralBinom_div`: `_root_.catalan m = Nat.centralBinom m / (m+1)`
3. Both give the same value: `Nat.mul_div_cancel` closes the `heq` bridge

Then:
- `_root_.catalan_succ'` gives convolution over `antidiagonal n`
- `Finset.Nat.sum_antidiagonal_eq_sum_range_succ` converts to `range (n+1)` sum

**Key insight**: The convolution does NOT need Vandermonde or generating functions —
bridging definitions via `Nat.mul_div_cancel` + `catalan_succ'` suffices.

### Files Modified
- `proofs/Proofs/CombinationsFormulaOQ02.lean` (314 lines, 0 sorries)

### PR
- #10487: https://github.com/rjwalters/lean-genius/pull/10487 (awaiting Docker build)

---

## Session 2026-04-03 (Session 1) — Progress: 5/6 Sorries Filled

**Mode**: FRESH
**Outcome**: progress — 5 sorries filled, 1 remains (catalan_convolution)

### What Was Done
- Created full proof file with ballot-formula definition
- Proved choose_2n_succ, catalan_mul_succ, catalan_pos
- Proved centralBinom_ge_two_pow (induction via Pascal+symmetry)
- Proved catalan_mono (nlinarith via catalan_step helper)
- Added centralBinom_succ_eq helper

### Remaining (Session 1 end)
- `catalan_convolution`: thought to need Vandermonde or generating functions

---

## Key Findings

- Ballot-formula definition (`C_n = C(2n,n) - C(2n,n+1)`) stays in ℕ (no division issues)
- `catalan_mul_succ` (our) + `catalan_eq_centralBinom_div` (Mathlib) establish the bridge
- `catalan_succ'` in `Mathlib.Combinatorics.Enumerative.Catalan` is the convolution over antidiagonal
- `Finset.Nat.sum_antidiagonal_eq_sum_range_succ` converts antidiagonal to range sum
- Absorption identity: `(2n+2)*C(2n+1,n+1) = C(2n+2,n+2)*(n+2)` (Nat.succ_mul_choose_eq)

---

## Built Items

- `proofs/Proofs/CombinationsFormulaOQ02.lean` — 314 lines, 0 sorries
  - 2 defs: catalan, centralBinom (abbrev)
  - 20+ theorems including catalan_convolution (proved)
  - 0 axioms
