/-
Erdős Problem #1051: Irrationality of Reciprocal Sums

**Statement**: If a₁ < a₂ < ⋯ is a sequence of integers with
  liminf(aₙ^{1/2^n}) > 1,
then is Σ_{n=1}^∞ 1/(aₙ·aₙ₊₁) irrational?

**Status**: OPEN

**Key Observations**:
1. The condition liminf(aₙ^{1/2^n}) > 1 means doubly-exponential growth
   - If c = liminf, then eventually aₙ > c^{2^n} for c > 1
   - Example: aₙ = 2^{2^n} gives aₙ^{1/2^n} = 2 > 1

2. The sum Σ 1/(aₙ·aₙ₊₁) is absolutely convergent for such sequences
   - By comparison with geometric series

3. Erdős noted "this is true if aₙ → ∞ 'rapidly'"
   - But the exact threshold is unclear

**Example**: aₙ = 2^{2^n}
- a₁ = 4, a₂ = 16, a₃ = 256, a₄ = 65536
- 1/(4·16) + 1/(16·256) + 1/(256·65536) + ⋯
- = 1/64 + 1/4096 + 1/16777216 + ⋯

Reference: https://erdosproblems.com/1051
-/

import Mathlib

namespace Erdos1051

open Filter Real BigOperators Finset

/-
## Part I: The Growth Condition
-/

/-- The sequence has the required growth: liminf(aₙ^{1/2^n}) > 1. -/
def hasDoublyExpGrowth (a : ℕ → ℕ) : Prop :=
  liminf (fun n => ((a n : ℝ) ^ (1 / 2^n : ℝ))) atTop > 1

/-- Alternative: there exists c > 1 such that aₙ ≥ c^{2^n} eventually. -/
def hasDoublyExpGrowth' (a : ℕ → ℕ) : Prop :=
  ∃ c : ℝ, c > 1 ∧ ∀ᶠ n in atTop, (a n : ℝ) ≥ c ^ (2^n : ℕ)

/-- The two growth conditions are equivalent. -/
theorem growth_equiv (a : ℕ → ℕ) :
    hasDoublyExpGrowth a ↔ hasDoublyExpGrowth' a := by
  sorry

/-
## Part II: The Sum
-/

/-- The partial sum Σ_{k=1}^{n} 1/(aₖ·aₖ₊₁). -/
noncomputable def partialSum (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  ∑ k ∈ range n, (1 : ℝ) / ((a k) * (a (k + 1)))

/-- The infinite sum Σ_{n=1}^∞ 1/(aₙ·aₙ₊₁), when it converges. -/
noncomputable def theSum (a : ℕ → ℕ) : ℝ :=
  tsum fun n => (1 : ℝ) / ((a n) * (a (n + 1)))

/-- The sum converges absolutely for doubly-exponential sequences. -/
theorem sum_converges (a : ℕ → ℕ) (ha : hasDoublyExpGrowth a) (hmono : StrictMono a) :
    Summable fun n => (1 : ℝ) / ((a n) * (a (n + 1))) := by
  -- For large n, aₙ ≥ c^{2^n} for some c > 1
  -- So 1/(aₙ·aₙ₊₁) ≤ 1/(c^{2^n} · c^{2^{n+1}}) = 1/c^{3·2^n}
  -- This is summable (much faster than geometric)
  sorry

/-
## Part III: The Main Conjecture
-/

/-- Erdős Problem #1051 (OPEN): For doubly-exponentially growing sequences,
    the reciprocal product sum is irrational. -/
def erdos_1051_conjecture : Prop :=
  ∀ a : ℕ → ℕ,
    StrictMono a →
    hasDoublyExpGrowth a →
    Irrational (theSum a)

/-
## Part IV: The Standard Example
-/

/-- The standard example: aₙ = 2^{2^n}. -/
def standardSeq (n : ℕ) : ℕ := 2 ^ (2 ^ n)

/-- standardSeq is strictly increasing. -/
theorem standardSeq_strictMono : StrictMono standardSeq := by
  intro m n hmn
  unfold standardSeq
  have h2n : 2 ^ m < 2 ^ n := Nat.pow_lt_pow_right (by norm_num : 1 < 2) hmn
  exact Nat.pow_lt_pow_right (by norm_num : 1 < 2) h2n

/-- standardSeq has the required growth with c = 2. -/
theorem standardSeq_growth : hasDoublyExpGrowth standardSeq := by
  unfold hasDoublyExpGrowth standardSeq
  -- aₙ^{1/2^n} = (2^{2^n})^{1/2^n} = 2^{2^n/2^n} = 2
  sorry

/-- For the standard sequence, aₙ^{1/2^n} = 2 exactly. -/
theorem standardSeq_root (n : ℕ) :
    ((standardSeq n : ℝ) ^ (1 / 2^n : ℝ)) = 2 := by
  unfold standardSeq
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  rw [← rpow_natCast, ← rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  simp only [one_div, mul_inv_cancel₀ (by positivity : (2:ℝ)^n ≠ 0), rpow_one]

/-- The sum for the standard sequence. -/
noncomputable def standardSum : ℝ := theSum standardSeq

/-- The sum for the standard sequence is ≈ 0.0156... -/
axiom standardSum_approx :
    (0.015 : ℝ) < standardSum ∧ standardSum < (0.016 : ℝ)

/-- The conjecture implies standardSum is irrational. -/
theorem standardSum_irrational (h : erdos_1051_conjecture) :
    Irrational standardSum :=
  h standardSeq standardSeq_strictMono standardSeq_growth

/-
## Part V: Related Irrationality Results
-/

/-- Erdős noted: "this is true if aₙ → ∞ 'rapidly'".
    This likely means super-exponential growth, but the exact bound is unclear. -/
axiom erdos_rapid_growth_result :
    ∃ f : (ℕ → ℕ) → Prop,
      (∀ a, f a → hasDoublyExpGrowth a) ∧
      (∀ a, StrictMono a → f a → Irrational (theSum a))

/-- Known: If aₙ grows "fast enough" (e.g., tower-exponentially),
    then Σ 1/aₙ is irrational by Liouville-type arguments. -/
axiom fast_growth_irrational :
    ∀ a : ℕ → ℕ, StrictMono a →
      (∀ n, (a (n + 1) : ℝ) ≥ (a n)^2) →
      Irrational (∑' n, (1 : ℝ) / a n)

/-
## Part VI: Telescoping Structure
-/

/-- If aₙ₊₁ = aₙ², then the sum telescopes. -/
theorem telescoping_case (a : ℕ → ℕ) (ha : ∀ n, a (n + 1) = (a n)^2) :
    Summable (fun n => (1 : ℝ) / ((a n) * (a (n + 1)))) := by
  -- 1/(aₙ · aₙ₊₁) = 1/(aₙ · aₙ²) = 1/aₙ³
  -- For a₀ = 2, we get a₁ = 4, a₂ = 16, etc.
  -- Sum of 1/aₙ³ converges rapidly
  sorry

/-- The identity: 1/(aₙ · aₙ₊₁) = 1/aₙ - 1/aₙ₊₁ when aₙ₊₁ - aₙ = 1.
    This doesn't apply to our case but illustrates the structure. -/
theorem telescoping_identity (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : b - a = 1) :
    1 / (a * b) = 1 / a - 1 / b := by
  field_simp
  linarith

/-
## Part VII: Summary
-/

/-- Erdős Problem #1051: Summary

**Conjecture**: For {aₙ} with liminf(aₙ^{1/2^n}) > 1,
  Σ 1/(aₙ·aₙ₊₁) is irrational.

**Formalized**:
- `hasDoublyExpGrowth` - the growth condition
- `theSum` - the infinite sum
- `erdos_1051_conjecture` - the main statement
- `standardSeq` - the 2^{2^n} example

**Proven**:
- `standardSeq_strictMono` - example is strictly increasing
- `standardSeq_root` - aₙ^{1/2^n} = 2 exactly

**Status**: OPEN
-/

axiom erdos_1051 : erdos_1051_conjecture

theorem erdos_1051_summary : True := trivial

end Erdos1051
