import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Tactic

/-
# Verified Recursive Legendre Symbol Computation

## What This Proves
The Law of Quadratic Reciprocity yields a GCD-like algorithm for computing
Legendre symbols. We implement this as an explicit recursive function in Lean 4
with a termination proof, answering the open question from the parent proof
(QuadraticReciprocityOQ03.lean):

  "Can the full Legendre symbol computation be implemented as a
   verified recursive function in Lean with a termination proof?"

Answer: **Yes.** The algorithm mirrors the Euclidean algorithm: at each step,
remove factors of 2, then use quadratic reciprocity to swap numerator and
denominator and take the remainder, strictly decreasing the first argument.

## Key Results
1. `jacobiAlgo` — Explicit recursive function with termination proof
2. `jacobiAlgo_eq_jacobiSym` — Correctness: equals Mathlib's `jacobiSym`
3. `legendreCompute_eq` — Corollary: equals `legendreSym` for primes

## The Algorithm (pseudocode)
  To compute (a/b) where b is odd and > 1, a > 0:
  1. If 4 | a: compute (a/4 | b) — squares don't affect the symbol
  2. If 2 | a: compute (a/2 | b) with sign adjustment (second supplementary law)
  3. If a = 1: return 1
  4. If a | b: return 0 (not coprime)
  5. Otherwise: swap via reciprocity (a/b) → ±(b mod a / a), recurse

  Terminates because a strictly decreases at each step:
  - Step 1: a/4 < a
  - Step 2: a/2 < a
  - Step 5: b mod a < a

## Mathlib Dependencies
- `jacobiSym.div_four_left` : J(a/4 | b) = J(a | b) when 4 | a and b odd
- `jacobiSym.even_odd` : second supplementary law for factor of 2
- `jacobiSym.quadratic_reciprocity_if` : reciprocity in if-then-else form
- `jacobiSym.mod_left` : J(a | b) depends only on a mod b
- `jacobiSym.eq_zero_iff` : J(a | b) = 0 iff not coprime

## Status
- [x] Recursive function with termination proof
- [x] Correctness proof (jacobiAlgo_eq_jacobiSym)
- [x] Connection to legendreSym (legendreCompute_eq)
- [x] Verified examples
- [x] Complete — 0 sorries, 0 axioms
-/

set_option linter.unusedVariables false

open NumberTheorySymbols

namespace LegendreCompute

-- ============================================================
-- PART 1: The Recursive Algorithm
-- ============================================================

/-- Recursive Jacobi symbol computation via quadratic reciprocity descent.

Computes `J(a | b)` (or `-J(a | b)` if `flip = true`) where `b` is odd and > 1.
The `flip` flag accumulates sign changes from reciprocity, avoiding intermediate
multiplication.

**Termination**: The first argument `a` strictly decreases at every recursive call,
exactly as in the Euclidean algorithm for GCD. -/
def jacobiAlgo (a b : ℕ) (flip : Bool) (ha : a > 0) : ℤ :=
  -- Step 1: Remove factor of 4 (a square, so (4/b) = 1)
  if h4 : a % 4 = 0 then
    jacobiAlgo (a / 4) b flip
      (Nat.div_pos (Nat.le_of_dvd ha (Nat.dvd_of_mod_eq_zero h4)) (by decide))
  -- Step 2: Remove factor of 2, adjust sign per (2/b) = χ₈(b)
  else if h2 : a % 2 = 0 then
    jacobiAlgo (a / 2) b (xor (b % 8 = 3 ∨ b % 8 = 5) flip)
      (Nat.div_pos (Nat.le_of_dvd ha (Nat.dvd_of_mod_eq_zero h2)) (by decide))
  -- Step 3: a is odd. If a = 1, the symbol is 1
  else if ha1 : a = 1 then
    if flip then -1 else 1
  -- Step 4: If a | b, then gcd(a,b) > 1, so symbol is 0
  else if hba : b % a = 0 then
    0
  -- Step 5: Quadratic reciprocity swap — (a/b) ↦ ±(b mod a / a)
  else
    jacobiAlgo (b % a) a (xor (a % 4 = 3 ∧ b % 4 = 3) flip)
      (Nat.pos_of_ne_zero hba)
termination_by a
decreasing_by
  · exact a.div_lt_self ha (by decide)  -- a/4 < a since a > 0
  · exact a.div_lt_self ha (by decide)  -- a/2 < a since a > 0
  · exact b.mod_lt ha                    -- b % a < a since a > 0

-- ============================================================
-- PART 2: Correctness Proof
-- ============================================================

/-- **Main correctness theorem.** The recursive algorithm computes the Jacobi symbol.

More precisely, `jacobiAlgo a b flip ha` equals `J(↑a | b)` when `flip = false`
and `-J(↑a | b)` when `flip = true`, provided `b` is odd and > 1.

The proof proceeds by strong induction on `a`, mirroring the recursive structure
of the algorithm. Each case uses the corresponding Mathlib lemma for the Jacobi
symbol. -/
theorem jacobiAlgo_eq_jacobiSym {a b : ℕ} {flip : Bool} {ha : a > 0}
    (hb2 : b % 2 = 1) (hb1 : b > 1) :
    jacobiAlgo a b flip ha = if flip then -J(↑a | b) else J(↑a | b) := by
  induction a using Nat.strongRecOn generalizing b flip with | ind a IH =>
  unfold jacobiAlgo
  -- Case 1: a % 4 = 0 — divide by 4 (square factor)
  split <;> rename_i h4
  · rw [IH (a / 4) (a.div_lt_self ha (by decide)) hb2 hb1]
    have key : J(↑(a / 4) | b) = J(↑a | b) := by
      conv_lhs => rw [show (↑(a / 4) : ℤ) = (↑a : ℤ) / 4 from by omega]
      exact jacobiSym.div_four_left (by exact_mod_cast h4) hb2
    cases flip <;> simp only [↓reduceIte, key, neg_inj]
  -- Case 2: a % 2 = 0 — divide by 2, adjust sign
  split <;> rename_i h2
  · rw [IH (a / 2) (a.div_lt_self ha (by decide)) hb2 hb1]
    have key : J(↑(a / 2) | b) = J(↑a / 2 | b) := by
      conv_lhs => rw [show (↑(a / 2) : ℤ) = (↑a : ℤ) / 2 from by omega]
    rw [key, ← jacobiSym.even_odd (by exact_mod_cast h2 : (↑a : ℤ) % 2 = 0) hb2]
    by_cases h : b % 8 = 3 ∨ b % 8 = 5 <;> simp [h]; cases flip <;> simp
  -- Case 3: a = 1 — base case
  split <;> rename_i ha1
  · subst ha1; simp
  -- Case 4: b % a = 0 — not coprime, symbol is 0
  split <;> rename_i hba
  · suffices J(↑a | b) = 0 by simp [this]
    refine jacobiSym.eq_zero_iff.mpr ⟨fun h => absurd (h ▸ hb1) (by decide), ?_⟩
    rwa [Int.gcd_natCast_natCast, Nat.gcd_eq_left (Nat.dvd_of_mod_eq_zero hba)]
  -- Case 5: Reciprocity swap
  · have ha_odd : a % 2 = 1 := by omega
    rw [IH (b % a) (b.mod_lt ha) ha_odd (by omega : a > 1)]
    suffices hsuff : J(↑(b % a) | a) = J(↑b | a) by
      rw [hsuff, ← jacobiSym.quadratic_reciprocity_if ha_odd hb2]
      by_cases h : a % 4 = 3 ∧ b % 4 = 3 <;> simp [h]; cases flip <;> simp
    rw [Int.natCast_mod]
    conv_rhs => rw [jacobiSym.mod_left (↑b) a]

-- ============================================================
-- PART 3: Legendre Symbol Connection
-- ============================================================

/-- Full Legendre symbol computation via the recursive algorithm.

Given `a : ℤ` and an odd prime `p`, reduces `a` mod `p` and delegates
to `jacobiAlgo` for the core recursion. -/
noncomputable def legendreCompute (a : ℤ) (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) : ℤ :=
  if hab : a % ↑p = 0 then 0
  else jacobiAlgo (a % ↑p).natAbs p false (Int.natAbs_pos.mpr hab)

/-- The recursive computation equals the Legendre symbol for odd primes.

This answers the open question: the Legendre symbol CAN be computed by a
verified recursive function with a termination proof. -/
theorem legendreCompute_eq (a : ℤ) (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    legendreCompute a p hp2 = legendreSym p a := by
  unfold legendreCompute
  rw [jacobiSym.legendreSym.to_jacobiSym]
  split_ifs with hab
  · -- a ≡ 0 (mod p): both sides are 0
    rw [jacobiSym.mod_left, hab, jacobiSym.zero_left (Nat.Prime.one_lt hp.out)]
  · -- Main case: reduce mod p, apply jacobiAlgo_eq_jacobiSym
    have hpodd : p % 2 = 1 := by have := hp.out.eq_two_or_odd; omega
    have hp1 : p > 1 := Nat.Prime.one_lt hp.out
    rw [jacobiAlgo_eq_jacobiSym hpodd hp1, if_neg Bool.false_ne_true,
        jacobiSym.mod_left a p,
        Int.natAbs_of_nonneg (Int.emod_nonneg a (Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero hp.out)))]

-- ============================================================
-- PART 4: Verified Example Computations
-- ============================================================

/-- (3/7) = -1: 3 is not a quadratic residue mod 7 -/
example : jacobiAlgo 3 7 false (by omega) = -1 := by native_decide

/-- (2/7) = 1: 2 is a QR mod 7, since 3² ≡ 2 (mod 7) -/
example : jacobiAlgo 2 7 false (by omega) = 1 := by native_decide

/-- (5/13) = -1 -/
example : jacobiAlgo 5 13 false (by omega) = -1 := by native_decide

/-- (7/11) = -1 -/
example : jacobiAlgo 7 11 false (by omega) = -1 := by native_decide

/-- (3/5) = -1: squares mod 5 are {0,1,4}, so 3 is not a QR -/
example : jacobiAlgo 3 5 false (by omega) = -1 := by native_decide

/-- (2/17) = 1: 17 ≡ 1 (mod 8), so 2 is a QR mod 17 -/
example : jacobiAlgo 2 17 false (by omega) = 1 := by native_decide

/-- (6/7) = -1: by multiplicativity, (6/7) = (2/7)·(3/7) = 1·(-1) = -1 -/
example : jacobiAlgo 6 7 false (by omega) = -1 := by native_decide

-- ============================================================
-- PART 5: Algorithm Properties
-- ============================================================

/-- The algorithm respects residue classes: J(a | b) = J(a mod b | b). -/
theorem jacobiAlgo_mod_left {a b : ℕ} {ha : a > 0}
    (hb2 : b % 2 = 1) (hb1 : b > 1) (hab : a % b > 0) :
    jacobiAlgo (a % b) b false hab = jacobiAlgo a b false ha := by
  rw [jacobiAlgo_eq_jacobiSym hb2 hb1, jacobiAlgo_eq_jacobiSym hb2 hb1,
      if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
  rw [Int.natCast_mod]
  conv_rhs => rw [jacobiSym.mod_left (↑a) b]

end LegendreCompute

-- ============================================================
-- Export main results
-- ============================================================

#check @LegendreCompute.jacobiAlgo
#check @LegendreCompute.jacobiAlgo_eq_jacobiSym
#check @LegendreCompute.legendreCompute_eq
