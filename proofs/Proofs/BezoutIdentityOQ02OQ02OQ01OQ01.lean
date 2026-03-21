/-
# Constructive Divisibility: Removing the Noncomputable Annotation

## Open Question Origin
From bezout-identity-oq-02-oq-02-oq-01:
"Can the noncomputable annotation be removed by making the divisibility
witness computable (e.g., via decidable divisibility)?"

## Answer: YES

The noncomputability in `constructive_div` came from using `hdvd.choose`
(Lean's classical choice). We replace it with computable integer division
`(b * c) / a`, which gives the same result when `a ∣ b * c`.

The key insight: we don't need the divisibility proof at runtime —
only at verification time. The algorithm itself only needs a, b, c.

## Status
- All theorems proved (0 sorries, 0 axioms)
- `constructive_div_computable` is NOT marked noncomputable
-/

import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Tactic

namespace BezoutConstructive

/-
═══════════════════════════════════════════════════════════════════════════════
PART I: THE EXTENDED EUCLIDEAN ALGORITHM (from parent file)
═══════════════════════════════════════════════════════════════════════════════ -/

/-- Extended Euclidean algorithm: returns (x, y, g) where a*x + b*y = g = gcd(a,b). -/
def extGcd : ℕ → ℕ → ℤ × ℤ × ℕ
  | a, 0 => (1, 0, a)
  | a, b + 1 =>
    have : a % (b + 1) < b + 1 := Nat.mod_lt a (Nat.succ_pos b)
    let r := extGcd (b + 1) (a % (b + 1))
    (r.2.1, r.1 - ↑(a / (b + 1)) * r.2.1, r.2.2)

theorem extGcd_gcd : ∀ (a b : ℕ), (extGcd a b).2.2 = Nat.gcd a b := by
  intro a b
  induction b using Nat.strongRecOn generalizing a with
  | ind b ih =>
    match b with
    | 0 => simp [extGcd, Nat.gcd_zero_right]
    | b + 1 =>
      simp [extGcd]; have hlt : a % (b + 1) < b + 1 := Nat.mod_lt a (Nat.succ_pos b)
      rw [ih (a % (b + 1)) hlt (b + 1)]
      rw [Nat.gcd_comm a (b + 1), Nat.gcd_rec (b + 1) a, Nat.gcd_comm]

theorem extGcd_bezout : ∀ (a b : ℕ),
    let r := extGcd a b
    (a : ℤ) * r.1 + (b : ℤ) * r.2.1 = (r.2.2 : ℤ) := by
  intro a b
  induction b using Nat.strongRecOn generalizing a with
  | ind b ih =>
    match b with
    | 0 => simp [extGcd]
    | b + 1 =>
      simp only; rw [show extGcd a (b + 1) =
        (let r := extGcd (b + 1) (a % (b + 1))
         (r.2.1, r.1 - ↑(a / (b + 1)) * r.2.1, r.2.2)) from by simp [extGcd]]
      simp only
      have hlt : a % (b + 1) < b + 1 := Nat.mod_lt a (Nat.succ_pos b)
      have hrec := ih (a % (b + 1)) hlt (b + 1)
      simp only at hrec
      set x' := (extGcd (b + 1) (a % (b + 1))).1
      set y' := (extGcd (b + 1) (a % (b + 1))).2.1
      have hdiv : (a : ℤ) = ↑(a / (b + 1)) * ↑(b + 1) + ↑(a % (b + 1)) := by
        have h := Nat.div_add_mod a (b + 1); zify at h ⊢; linarith
      linear_combination hrec + hdiv * y'

theorem extGcd_correct (a b : ℕ) :
    let r := extGcd a b
    (a : ℤ) * r.1 + (b : ℤ) * r.2.1 = ↑(Nat.gcd a b) := by
  have hbez := extGcd_bezout a b; have hgcd := extGcd_gcd a b
  simp only; rw [← hgcd]; exact hbez

/-
═══════════════════════════════════════════════════════════════════════════════
PART II: THE FULLY COMPUTABLE CONSTRUCTIVE QUOTIENT
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Fully computable constructive quotient**.
    Given coprime a, b : ℕ, compute q = x*c + y*(b*c/a) where
    x, y are Bézout coefficients from extGcd.

    This is NOT marked noncomputable — the divisibility witness
    `(b * c) / a` is computed via integer division, not classical choice.

    Compare with the parent file's `constructive_div` which used
    `hdvd.choose` and required the `noncomputable` annotation. -/
def constructive_div_computable (a b c : ℕ) : ℤ :=
  let r := extGcd a b
  let x := r.1
  let y := r.2.1
  let k := ((b : ℤ) * c) / (a : ℤ)
  x * c + y * k

/-- The computable constructive quotient is correct: a * q = c. -/
theorem constructive_div_computable_correct (a b c : ℕ)
    (hcop : Nat.gcd a b = 1) (hdvd : (a : ℤ) ∣ (b : ℤ) * c)
    (ha : (a : ℤ) ≠ 0) :
    (a : ℤ) * constructive_div_computable a b c = (c : ℤ) := by
  unfold constructive_div_computable
  set r := extGcd a b
  set x := r.1
  set y := r.2.1
  set k := ((b : ℤ) * c) / (a : ℤ)
  -- k is the correct divisibility witness: a * k = b * c
  have hk : (b : ℤ) * c = (a : ℤ) * k := by
    rw [show k = ((b : ℤ) * c) / (a : ℤ) from rfl]
    exact (Int.mul_ediv_cancel' hdvd).symm
  -- Bézout identity: a * x + b * y = 1
  have hbez : (a : ℤ) * x + (b : ℤ) * y = 1 := by
    have h := extGcd_correct a b
    simp only at h; rw [hcop] at h; simp at h; linarith
  -- Core formula: a * (x * c + y * k) = (x * a + y * b) * c = 1 * c = c
  calc (a : ℤ) * (x * ↑c + y * k)
      = x * ↑a * ↑c + y * (↑a * k) := by ring
    _ = x * ↑a * ↑c + y * (↑b * ↑c) := by rw [← hk]
    _ = (↑a * x + ↑b * y) * ↑c := by ring
    _ = 1 * ↑c := by rw [hbez]
    _ = ↑c := one_mul _

/-- **Computable Euclid's lemma**: extract a divisibility witness computably. -/
theorem euclids_lemma_computable (a b c : ℕ)
    (hcop : Nat.gcd a b = 1) (hdvd : (a : ℤ) ∣ (b : ℤ) * c)
    (ha : (a : ℤ) ≠ 0) :
    (a : ℤ) ∣ (c : ℤ) :=
  ⟨constructive_div_computable a b c,
   (constructive_div_computable_correct a b c hcop hdvd ha).symm⟩

/-
═══════════════════════════════════════════════════════════════════════════════
PART III: DEMONSTRATING COMPUTABILITY
═══════════════════════════════════════════════════════════════════════════════ -/

-- The function evaluates without any sorry, axiom, or noncomputable usage.
-- 3 ∣ 7*6 = 42, so q such that 3*q = 6, i.e. q = 2
example : constructive_div_computable 3 7 6 = 2 := by native_decide

-- 5 ∣ 7*10 = 70, so q such that 5*q = 10, i.e. q = 2
example : constructive_div_computable 5 7 10 = 2 := by native_decide

-- Verify correctness: 3 * q = 6
example : (3 : ℤ) * constructive_div_computable 3 7 6 = 6 := by native_decide

-- Verify correctness: 5 * q = 10
example : (5 : ℤ) * constructive_div_computable 5 7 10 = 10 := by native_decide

-- #eval demonstrates computability (no noncomputable needed)
#eval constructive_div_computable 3 7 6    -- 2
#eval constructive_div_computable 5 7 10   -- 2
#eval constructive_div_computable 7 11 77  -- 11 (since 7*11 = 77, q = 77/7 = 11)
#eval constructive_div_computable 13 17 26 -- 2 (since 13*2 = 26)

/-
═══════════════════════════════════════════════════════════════════════════════
PART IV: THE KEY INSIGHT — WHY THIS WORKS
═══════════════════════════════════════════════════════════════════════════════ -/

/-- The divisibility witness via integer division equals the classical one.
    When `a ∣ bc`, `bc / a` gives the same value as the classical witness.
    This is what lets us remove `noncomputable`. -/
theorem div_witness_correct (a : ℤ) (bc : ℤ) (hdvd : a ∣ bc) (ha : a ≠ 0) :
    a * (bc / a) = bc := by
  exact Int.mul_ediv_cancel' hdvd

/-
═══════════════════════════════════════════════════════════════════════════════
VERIFICATION
═══════════════════════════════════════════════════════════════════════════════ -/

#check @constructive_div_computable          -- NOT noncomputable
#check @constructive_div_computable_correct
#check @euclids_lemma_computable
#check @div_witness_correct

end BezoutConstructive
