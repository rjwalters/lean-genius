/-
  Aristotle targets for Erdos818 (Product Set Lower Bound for Small Sumsets)
  Routine supporting lemmas for automated proof search.
  See Erdos818Problem.lean for the main formalization.

  These lemmas provide building blocks for sum-product analysis:
  - log arithmetic helpers (log positivity, monotonicity)
  - Algebraic simplifications for c * x^2 / log x bounds
  - productSet and sumset basic properties
  - Cauchy-Schwarz energy bound helpers
  - Multiplicative energy basic properties
-/
import Mathlib

open Real Finset

namespace Erdos818.Aristotle

/-
  ## Section 1: Log Arithmetic Helpers
-/

/-- log |A| ≥ log 2 for |A| ≥ 2 -/
lemma log_card_ge_log2 (A : Finset ℤ) (hA : A.card ≥ 2) :
    Real.log A.card ≥ Real.log 2 :=
  Real.log_le_log (by norm_num) (by exact_mod_cast hA)

/-- log n > 0 for n ≥ 3 -/
lemma log_pos_of_ge_three (n : ℕ) (hn : n ≥ 3) : Real.log n > 0 :=
  Real.log_pos (by exact_mod_cast show 1 < n from by omega)

/-- log n > 0 for n ≥ 2 -/
lemma log_pos_of_ge_two (n : ℕ) (hn : n ≥ 2) : Real.log n > 0 :=
  Real.log_pos (by exact_mod_cast show 1 < n from by omega)

/-- n^2 / log n^1 = n^2 / log n -/
lemma rpow_one_eq (x : ℝ) : x ^ (1 : ℝ) = x :=
  Real.rpow_one x

/-- c * x / y ≥ x / y when c ≥ 1 and y > 0 -/
lemma mul_div_ge_div (c x y : ℝ) (hc : c ≥ 1) (hy : y > 0) :
    c * x / y ≥ x / y := by
  sorry

/-- c * x^2 / log n ≥ x^2 / log n when c ≥ 1 -/
lemma const_sq_div_log_ge (c x : ℝ) (n : ℕ) (hc : c ≥ 1) (hlog : Real.log n > 0) :
    c * x ^ 2 / Real.log n ≥ x ^ 2 / Real.log n :=
  (div_le_div_right hlog).mpr (by nlinarith [sq_nonneg x])

/-
  ## Section 2: Sumset and productSet Properties
-/

/-- The sumset A + A is nonempty for nonempty A -/
lemma sumset_nonempty (A : Finset ℤ) (hA : A.Nonempty) :
    (A + A : Finset ℤ).Nonempty := by
  obtain ⟨a, ha⟩ := hA
  exact ⟨a + a, Finset.mem_add.mpr ⟨a, ha, a, ha, rfl⟩⟩

/-- |A + A| ≥ |A| (trivially: a + a ∈ A + A for a ∈ A) -/
lemma sumset_card_ge (A : Finset ℤ) :
    (A + A : Finset ℤ).card ≥ A.card :=
  calc A.card = (A.image (fun a => a + a)).card :=
        (Finset.card_image_of_injective A (fun a b h => by linarith)).symm
    _ ≤ (A + A : Finset ℤ).card :=
        Finset.card_le_card (fun x hx => by
          obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
          exact Finset.mem_add.mpr ⟨a, ha, a, ha, rfl⟩)

/-- |A * A| ≥ |A| (trivially: a * a ∈ A * A for a ∈ A) -/
lemma productSet_card_ge (A : Finset ℤ) (hA : A.Nonempty) :
    (A * A : Finset ℤ).card ≥ 1 := by
  obtain ⟨a, ha⟩ := hA
  exact Finset.card_pos.mpr ⟨a * a, Finset.mem_mul.mpr ⟨a, ha, a, ha, rfl⟩⟩

/-
  ## Section 3: Multiplicative Energy Helpers
-/

/-- The multiplicative energy E×(A) counts 4-tuples with a*b = c*d -/
noncomputable def multEnergy (A : Finset ℤ) : ℕ :=
  ((A ×ˢ A) ×ˢ (A ×ˢ A)).filter (fun ((a, b), (c, d)) => a * b = c * d) |>.card

/-- E×(A) ≥ |A|^2 (at least the diagonal pairs (a,a), (a,a)) -/
lemma multEnergy_ge_sq (A : Finset ℤ) : multEnergy A ≥ A.card ^ 2 := by
  sorry

/-- Cauchy-Schwarz: E×(A) * |A*A| ≥ |A|^4 -/
lemma cauchy_schwarz_energy (A : Finset ℤ) (hA : A.card ≥ 2) :
    (multEnergy A : ℝ) * (A * A : Finset ℤ).card ≥ (A.card : ℝ) ^ 4 := by
  sorry

/-
  ## Section 4: Bound Arithmetic
-/

/-- (a / b)^2 = a^2 / b^2 for reals -/
lemma div_sq (a b : ℝ) : (a / b) ^ 2 = a ^ 2 / b ^ 2 :=
  div_pow a b 2

/-- a^4 / a^2 = a^2 for positive a -/
lemma pow4_div_pow2 (a : ℝ) (ha : a > 0) : a ^ 4 / a ^ 2 = a ^ 2 := by
  have h : a ^ 2 > 0 := pow_pos ha 2
  field_simp [h.ne']
  ring

/-- a^2 / (K * log n) = a^2 / K / log n -/
lemma div_assoc_log (a K logn : ℝ) (hK : K > 0) (hl : logn > 0) :
    a ^ 2 / (K * logn) = a ^ 2 / K / logn := by
  field_simp [hK.ne', hl.ne']
  ring

end Erdos818.Aristotle
