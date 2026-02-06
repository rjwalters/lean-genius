/-
  Erdős Problem #285: Egyptian Fractions Asymptotics

  **Question**: Let f(k) be the minimal value of the largest denominator nₖ
  among all representations 1 = 1/n₁ + ··· + 1/nₖ with n₁ < n₂ < ··· < nₖ.
  Is it true that f(k) = (1 + o(1)) · e/(e-1) · k?

  **Answer**: YES — proved by Greg Martin (2000).

  The constant e/(e-1) ≈ 1.582 arises from the harmonic series structure:
  the reciprocals in [e, e·u] sum to approximately 1, contributing ~(e-1)·u terms.

  Reference: https://erdosproblems.com/285
  Key paper: Martin, Greg, "Denser Egyptian fractions" (2000)
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Complex.ExponentialBounds

namespace Erdos285

open Finset Filter Real BigOperators
open scoped Topology Real

/- ## Background on Egyptian Fractions -/

/--
An Egyptian fraction representation of 1 using k terms is a strictly increasing
sequence n₁ < n₂ < ··· < nₖ of positive integers such that
1 = 1/n₁ + 1/n₂ + ··· + 1/nₖ

Note: k+1 terms because we index from 0 to k (Fin k.succ).
-/
def IsEgyptianRepresentation (k : ℕ) (n : Fin k.succ → ℕ) : Prop :=
  StrictMono n ∧ 0 ∉ Set.range n ∧ 1 = ∑ i, (1 : ℝ) / n i

/--
The set of k for which Egyptian fraction representations with k+1 terms exist.
(Representations always exist for k ≥ 2 since 1 = 1/2 + 1/3 + 1/6.)
-/
def ValidLengths : Set ℕ :=
  {k | ∃ n : Fin k.succ → ℕ, IsEgyptianRepresentation k n}

/--
f(k) is the minimal value of the largest denominator nₖ among all
Egyptian fraction representations of 1 using k+1 terms.
-/
noncomputable def f (k : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ n : Fin k.succ → ℕ, IsEgyptianRepresentation k n ∧ n (Fin.last k) = m}

/- ## The Main Asymptotic Result -/

/--
The constant e/(e-1) ≈ 1.5819... that appears in the asymptotics.
-/
noncomputable def egyptianConstant : ℝ := rexp 1 / (rexp 1 - 1)

/--
**Martin (2000)**: f(k) = (1 + o(1)) · e/(e-1) · k.

The minimal largest denominator in a k+1-term Egyptian fraction representation
of 1 is asymptotically e/(e-1) times k.
-/
axiom martin_egyptian_fractions :
    ∃ (o : ℕ → ℝ) (_ : Asymptotics.IsLittleO atTop o (fun _ : ℕ => (1 : ℝ))),
      ∀ k ∈ ValidLengths, (f k : ℝ) = (1 + o k) * egyptianConstant * (k + 1)

/-- Erdős Problem #285: The asymptotic formula holds -/
theorem erdos_285 :
    ∃ (o : ℕ → ℝ), (Asymptotics.IsLittleO atTop o (fun _ => (1 : ℝ))) ∧
      ∀ k ∈ ValidLengths, (f k : ℝ) = (1 + o k) * egyptianConstant * (k + 1) :=
  let ⟨o, ho, hf⟩ := martin_egyptian_fractions
  ⟨o, ho, hf⟩

/- ## The Lower Bound (Trivial) -/

/--
**Lower Bound**: f(k) ≥ (1 + o(1)) · e/(e-1) · k.
This follows directly from Martin's asymptotic equality (equality implies ≤).
-/
theorem egyptian_lower_bound :
    ∃ (o : ℕ → ℝ) (_ : Asymptotics.IsLittleO atTop o (fun _ : ℕ => (1 : ℝ))),
      ∀ k ∈ ValidLengths, (1 + o k) * egyptianConstant * (k + 1) ≤ f k := by
  obtain ⟨o, ho, hf⟩ := martin_egyptian_fractions
  exact ⟨o, ho, fun k hk => le_of_eq (hf k hk).symm⟩

/- ## Understanding the Constant -/

/-
The value e/(e-1) ≈ 1.5819 means:
- For k=100 terms: f(100) ≈ 158 (largest denominator ~158)
- For k=1000 terms: f(1000) ≈ 1582

The constant arises because ln(e·u) - ln(e) = 1 for any u,
so the interval [e, e·u] contains approximately 1 unit of "harmonic mass".
-/

/-- e/(e-1) > 1, showing f(k) > k always -/
theorem egyptianConstant_gt_one : egyptianConstant > 1 := by
  unfold egyptianConstant
  have he : rexp 1 > 1 := Real.one_lt_exp_iff.mpr (by norm_num : (1 : ℝ) > 0)
  have hpos : rexp 1 - 1 > 0 := by linarith
  rw [gt_iff_lt, one_lt_div hpos]
  linarith

/-- e/(e-1) < 2, so f(k) < 2k asymptotically.
    Proof: e > 2 (from exp bounds), so e - 1 > 1, so 1/(e-1) < 1,
    so e/(e-1) = 1 + 1/(e-1) < 2. -/
theorem egyptianConstant_lt_two : egyptianConstant < 2 := by
  unfold egyptianConstant
  have he : rexp 1 > 2 := by linarith [Real.exp_one_gt_d9]
  have hpos : rexp 1 - 1 > 0 := by linarith
  rw [div_lt_iff₀ hpos]
  nlinarith

/-- e/(e-1) > 3/2, a tighter lower bound showing f(k) > 1.5k asymptotically.
    Proof: e < 2.72 (from exp bounds), so e-1 < 1.72, so 1/(e-1) > 1/1.72 > 0.5,
    so e/(e-1) = 1 + 1/(e-1) > 1.5. -/
theorem egyptianConstant_gt_three_halves : egyptianConstant > 3 / 2 := by
  unfold egyptianConstant
  have he_lower : rexp 1 > 2 := by linarith [Real.exp_one_gt_d9]
  have he_upper : rexp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hpos : rexp 1 - 1 > 0 := by linarith
  rw [gt_iff_lt, lt_div_iff₀ hpos]
  nlinarith

/-- The Egyptian constant is positive. -/
theorem egyptianConstant_pos : egyptianConstant > 0 := by
  linarith [egyptianConstant_gt_one]

/-- e/(e-1) = 1 + 1/(e-1): the constant decomposes as 1 plus the reciprocal gap. -/
theorem egyptianConstant_eq : egyptianConstant = 1 + 1 / (rexp 1 - 1) := by
  unfold egyptianConstant
  have hpos : rexp 1 - 1 > 0 := by
    have : rexp 1 > 1 := Real.one_lt_exp_iff.mpr (by norm_num : (1 : ℝ) > 0)
    linarith
  field_simp
  ring

/-- The reciprocal of the Egyptian constant is (e-1)/e = 1 - 1/e.
    This is the "density" of usable denominators: in any range [a, ea],
    a fraction (e-1)/e of the integers contribute useful unit fractions. -/
theorem egyptianConstant_inv : egyptianConstant⁻¹ = 1 - (rexp 1)⁻¹ := by
  unfold egyptianConstant
  have he_pos : rexp 1 > 0 := exp_pos 1
  have hpos : rexp 1 - 1 > 0 := by
    have : rexp 1 > 1 := Real.one_lt_exp_iff.mpr (by norm_num : (1 : ℝ) > 0)
    linarith
  rw [inv_div]
  field_simp

/- ## Concrete Valid Lengths -/

/-- k = 2 is a valid length: 1 = 1/2 + 1/3 + 1/6 (3 terms). -/
theorem two_mem_validLengths : 2 ∈ ValidLengths := by
  refine ⟨![2, 3, 6], ?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Matrix.cons_val_zero, Matrix.cons_val_one]
  · simp
  · simp [Fin.sum_univ_succ, Matrix.cons_val_zero]
    norm_num

/-- k = 3 is a valid length: 1 = 1/2 + 1/4 + 1/5 + 1/20 (4 terms). -/
theorem three_mem_validLengths : 3 ∈ ValidLengths := by
  refine ⟨![2, 4, 5, 20], ?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Matrix.cons_val_zero, Matrix.cons_val_one]
  · simp
  · simp [Fin.sum_univ_succ, Matrix.cons_val_zero]
    norm_num

/-- k = 4 is a valid length: 1 = 1/3 + 1/4 + 1/5 + 1/6 + 1/20 (5 terms). -/
theorem four_mem_validLengths : 4 ∈ ValidLengths := by
  refine ⟨![3, 4, 5, 6, 20], ?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Matrix.cons_val_zero, Matrix.cons_val_one]
  · simp
  · simp [Fin.sum_univ_succ, Matrix.cons_val_zero]
    norm_num

/-- Tighter lower bound: e/(e-1) > 79/50.
    We need e > 79/50 * (e-1) = 79e/50 - 79/50, i.e., e(1 - 79/50) > -79/50,
    i.e., -29e/50 > -79/50, i.e., 29e < 79 * 2 = 158, need e < 158/29 ≈ 5.45. True. -/
theorem egyptianConstant_gt_79_over_50 : egyptianConstant > 79 / 50 := by
  unfold egyptianConstant
  have he_lower : rexp 1 > 2.718281828 := by linarith [Real.exp_one_gt_d9]
  have hpos : rexp 1 - 1 > 0 := by linarith
  -- e/(e-1) > 79/50 iff 50*e > 79*(e-1) = 79e - 79 iff 79 > 29e iff e < 79/29
  -- Since e < 2.72 < 79/29 ≈ 2.724, this is true
  rw [gt_iff_lt, lt_div_iff₀ hpos]
  have he_upper : rexp 1 < 2.7182818286 := Real.exp_one_lt_d9
  -- Goal: 79/50 * (rexp 1 - 1) < rexp 1
  -- i.e., 79*(rexp 1 - 1) < 50 * rexp 1
  -- i.e., 79*rexp 1 - 79 < 50*rexp 1
  -- i.e., 29*rexp 1 < 79
  -- 29 * 2.7182818286 < 29 * 2.72 = 78.88 < 79. True.
  nlinarith

/- ## Examples -/

/-- The classic 3-term representation: 1 = 1/2 + 1/3 + 1/6 -/
example : (1 : ℝ) / 2 + 1 / 3 + 1 / 6 = 1 := by norm_num

/-- Another representation: 1 = 1/2 + 1/4 + 1/5 + 1/20 -/
example : (1 : ℝ) / 2 + 1 / 4 + 1 / 5 + 1 / 20 = 1 := by norm_num

/-- And: 1 = 1/3 + 1/4 + 1/5 + 1/6 + 1/20 -/
example : (1 : ℝ) / 3 + 1 / 4 + 1 / 5 + 1 / 6 + 1 / 20 = 1 := by norm_num

/- ## Additional Valid Lengths -/

/-- k = 0 is a valid length: 1 = 1/1 (1 term). -/
theorem zero_mem_validLengths : 0 ∈ ValidLengths := by
  refine ⟨![1], ?_, ?_, ?_⟩
  · intro i j hij
    exact absurd (Fin.ext_iff.mpr (by omega : i.val = j.val) |>.symm ▸ hij) (lt_irrefl _)
  · simp
  · simp

/- ## Additional Properties -/

/-- k = 1 is NOT a valid length: there is no way to write 1 = 1/a + 1/b with a < b.
    Proof: clearing denominators gives a + b = ab. With a,b positive integers and a < b,
    this forces a = b = 2 (unique solution), contradicting a < b. -/
theorem one_not_mem_validLengths : 1 ∉ ValidLengths := by
  intro ⟨n, hstrict, hnonzero, hsum⟩
  have h01 : n 0 < n 1 := hstrict (by omega : (0 : Fin 2) < 1)
  have hn0_pos : 0 < n 0 := by
    by_contra h; push_neg at h
    have heq : n 0 = 0 := Nat.le_zero.mp h
    exact hnonzero (Set.mem_range.mpr ⟨0, heq⟩)
  have hn1_pos : 0 < n 1 := by omega
  -- Get: (1 : ℝ) = (↑(n 0))⁻¹ + (↑(n 1))⁻¹ from the Finset sum
  have hcalc : (1 : ℝ) = (↑(n 0) : ℝ)⁻¹ + (↑(n 1) : ℝ)⁻¹ := by
    simp [Fin.sum_univ_succ] at hsum; exact hsum
  -- Clear denominators in ℝ: n0 * n1 = n0 + n1
  have h0 : (n 0 : ℝ) > 0 := Nat.cast_pos.mpr hn0_pos
  have h1 : (n 1 : ℝ) > 0 := Nat.cast_pos.mpr hn1_pos
  have hmul_real : (↑(n 0) : ℝ) * ↑(n 1) = ↑(n 0) + ↑(n 1) := by
    have h := hcalc
    rw [inv_eq_one_div, inv_eq_one_div] at h
    field_simp at h
    linarith
  -- Transfer to ℕ
  have hnat : n 0 * n 1 = n 0 + n 1 := by exact_mod_cast hmul_real
  -- In ℕ: a*b = a + b with a ≥ 1 and a < b has no solutions
  -- Key: n0 ≤ 2 (from n0 * n1 = n0 + n1 and n1 ≥ n0 + 1)
  have hn0_le : n 0 ≤ 2 := by
    -- n0 * n1 = n0 + n1 with n1 ≥ n0 + 1
    -- n0 * (n0 + 1) ≤ n0 * n1 = n0 + n1 ≤ n0 + n0 * n1 ... wrong direction
    -- Better: n0 * n1 = n0 + n1, so n0 * (n1 - 1) = n1 (for n1 ≥ 1)
    -- n1 ≥ n0 + 1 means n1 - 1 ≥ n0, so n0 * n0 ≤ n0 * (n1 - 1)
    -- We need to be careful with ℕ subtraction
    -- From n0 * n1 = n0 + n1: n0 * n1 - n1 = n0, i.e., n1 * (n0 - 1) = n0
    -- For n0 ≥ 3: n1 * (n0 - 1) ≥ n1 * 2 ≥ (n0+1)*2 ≥ 8 > 3 ≥ n0. Contradiction!
    by_contra h; push_neg at h
    -- n 0 ≥ 3
    have : n 0 ≥ 3 := by omega
    -- n 0 * n 1 = n 0 + n 1 implies n 0 * n 1 ≤ 2 * n 1 (since n 0 ≤ n 1)
    -- Actually n 0 * n 1 ≥ 3 * (n 0 + 1) since n 1 ≥ n 0 + 1 ≥ 4
    have : n 1 ≥ 4 := by omega
    -- n 0 * n 1 ≥ 3 * 4 = 12
    -- n 0 + n 1 ≤ n 1 - 1 + n 1 = 2 * n 1 - 1
    -- Actually both are complicated. Let nlinarith try with the bound.
    nlinarith
  interval_cases (n 0)
  · omega  -- n 0 = 1: n 1 = 1 + n 1, impossible
  · omega  -- n 0 = 2: 2 * n 1 = 2 + n 1, n 1 = 2, but 2 < 2 is false

/-- k = 5 is a valid length: 1 = 1/3 + 1/4 + 1/5 + 1/6 + 1/21 + 1/420 (6 terms).
    Decomposition: 1/20 = 1/21 + 1/420 applied to the k=4 witness. -/
theorem five_mem_validLengths : 5 ∈ ValidLengths := by
  refine ⟨![3, 4, 5, 6, 21, 420], ?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Matrix.cons_val_zero, Matrix.cons_val_one]
  · simp
  · simp [Fin.sum_univ_succ, Matrix.cons_val_zero]
    norm_num

/-- Example: 1 = 1/3 + 1/4 + 1/5 + 1/6 + 1/21 + 1/420 -/
example : (1 : ℝ) / 3 + 1 / 4 + 1 / 5 + 1 / 6 + 1 / 21 + 1 / 420 = 1 := by norm_num

/- ## Structural Properties -/

/--
**Strictly increasing positive sequences have large last elements:**
If n : Fin (k+1) → ℕ is strictly increasing with all values positive,
then n(last k) ≥ k + 1.
-/
theorem strict_mono_last_ge_succ {k : ℕ} {n : Fin k.succ → ℕ}
    (hstrict : StrictMono n) (hpos : 0 ∉ Set.range n) :
    n (Fin.last k) ≥ k + 1 := by
  -- Each n(i) ≥ i.val + 1 by induction on i.val
  suffices h : ∀ i : Fin k.succ, n i ≥ i.val + 1 by
    have := h (Fin.last k)
    simp [Fin.last] at this
    exact this
  intro ⟨i, hi⟩
  induction i with
  | zero =>
    have hne : n ⟨0, hi⟩ ≠ 0 := by
      intro heq
      exact hpos (Set.mem_range.mpr ⟨⟨0, hi⟩, heq⟩)
    show n ⟨0, hi⟩ ≥ (⟨0, hi⟩ : Fin k.succ).val + 1
    show n ⟨0, hi⟩ ≥ 0 + 1
    omega
  | succ j ih =>
    have hj : j < k.succ := by omega
    have ihj := ih hj
    show n ⟨j + 1, hi⟩ ≥ (⟨j + 1, hi⟩ : Fin k.succ).val + 1
    show n ⟨j + 1, hi⟩ ≥ j + 1 + 1
    have hlt : (⟨j, hj⟩ : Fin k.succ) < ⟨j + 1, hi⟩ := by
      exact Fin.mk_lt_mk.mpr (by omega)
    have hmon := hstrict hlt
    change n ⟨j, hj⟩ ≥ (⟨j, hj⟩ : Fin k.succ).val + 1 at ihj
    change n ⟨j, hj⟩ ≥ j + 1 at ihj
    omega

/--
**f is defined on valid lengths:**
If k ∈ ValidLengths, then the set of achievable largest denominators is nonempty.
-/
theorem f_set_nonempty (k : ℕ) (hk : k ∈ ValidLengths) :
    ∃ m : ℕ, ∃ n : Fin k.succ → ℕ, IsEgyptianRepresentation k n ∧ n (Fin.last k) = m := by
  obtain ⟨n, hn⟩ := hk
  exact ⟨n (Fin.last k), n, hn, rfl⟩

/--
**Trivial lower bound**: For valid lengths, f(k) ≥ k+1.
Any strictly increasing sequence of positive integers starting from ≥ 1 must have
its (k+1)-th element ≥ k+1, so the sInf of all such last elements is ≥ k+1.
-/
theorem f_ge_succ (k : ℕ) (hk : k ∈ ValidLengths) : f k ≥ k + 1 := by
  unfold f
  apply le_csInf
  · obtain ⟨m, hm⟩ := f_set_nonempty k hk
    exact ⟨m, hm⟩
  · intro m ⟨n, hn, hlast⟩
    rw [← hlast]
    exact strict_mono_last_ge_succ hn.1 hn.2.1

/--
**Egyptian constant is in (3/2, 2).**
Combines the previously established bounds into a single statement.
-/
theorem egyptianConstant_in_interval : 3 / 2 < egyptianConstant ∧ egyptianConstant < 2 :=
  ⟨egyptianConstant_gt_three_halves, egyptianConstant_lt_two⟩

/--
**The Egyptian constant as 1 + 1/(e-1).**
This form is useful for understanding the relationship to the harmonic series.
-/
theorem egyptianConstant_eq_one_plus_inv :
    egyptianConstant = 1 + (rexp 1 - 1)⁻¹ := by
  unfold egyptianConstant
  have hpos : rexp 1 - 1 > 0 := by
    have : rexp 1 > 1 := Real.one_lt_exp_iff.mpr (by norm_num : (1 : ℝ) > 0)
    linarith
  rw [div_eq_iff (ne_of_gt hpos)]
  rw [add_mul, one_mul, inv_mul_cancel₀ (ne_of_gt hpos)]
  ring

/--
**The product e·(e-1)⁻¹ is well-defined.**
Both factors are positive, confirming the constant makes sense.
-/
theorem egyptianConstant_well_defined : rexp 1 > 0 ∧ rexp 1 - 1 > 0 :=
  ⟨exp_pos 1, by have : rexp 1 > 1 := Real.one_lt_exp_iff.mpr (by norm_num : (1 : ℝ) > 0); linarith⟩

end Erdos285
