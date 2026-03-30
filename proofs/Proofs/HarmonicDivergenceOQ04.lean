/-
Generalizing Oresme's Grouping Argument: The Cauchy Condensation Test

Source: Open question from harmonic-divergence gallery proof
Status: VERIFIED (0 axioms, 0 sorries)

This formalization shows that Oresme's grouping argument (1350) for the harmonic
series generalizes to the Cauchy condensation test, which completely characterizes
convergence/divergence for monotone decreasing nonneg sequences:

  For f : ℕ → ℝ with f ≥ 0 and f antitone:
    Σ f(n) converges  ⟺  Σ 2^k · f(2^k) converges

We prove:
1. The condensation characterization (from Mathlib)
2. Oresme's harmonic divergence as a special case of condensation
3. The constant sequence 1 is not summable (condensed harmonic = Σ 1)
4. Concordance with Mathlib's direct `not_summable_one_div_natCast`
-/

import Mathlib

open Finset Filter BigOperators Topology Real

namespace HarmonicDivergenceOQ04

/-! ## Part I: The Cauchy Condensation Test

The Cauchy condensation test states that for a nonneg antitone sequence f,
Σ f(n) converges if and only if Σ 2^k · f(2^k) converges. This generalizes
Oresme's grouping argument from the 14th century. -/

/-- The Cauchy condensation test for real-valued sequences: Σ f(n) is summable
    iff Σ 2^k · f(2^k) is summable, provided f is nonneg and antitone on positives.
    This wraps Mathlib's `summable_condensed_iff_of_nonneg`. -/
theorem cauchy_condensation_test {f : ℕ → ℝ}
    (hf_nonneg : ∀ n, 0 ≤ f n)
    (hf_anti : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m) :
    Summable f ↔ Summable (fun k => (2 : ℝ) ^ k * f (2 ^ k)) :=
  (summable_condensed_iff_of_nonneg hf_nonneg hf_anti).symm

/-- Contrapositive: Σ f(n) diverges iff Σ 2^k · f(2^k) diverges. -/
theorem cauchy_condensation_diverges {f : ℕ → ℝ}
    (hf_nonneg : ∀ n, 0 ≤ f n)
    (hf_anti : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m) :
    ¬Summable f ↔ ¬Summable (fun k => (2 : ℝ) ^ k * f (2 ^ k)) := by
  rw [cauchy_condensation_test hf_nonneg hf_anti]

/-! ## Part II: Oresme's Argument as a Special Case

Oresme's 14th-century proof that Σ 1/n diverges is exactly the condensation
test applied to f(n) = 1/n: the condensed series Σ 2^k · 1/2^k = Σ 1 = ∞. -/

/-- 1/n is nonneg for all n : ℕ. -/
theorem one_div_nonneg_nat (n : ℕ) : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity

/-- 1/n is antitone for positive n: m ≤ n → 1/n ≤ 1/m. -/
theorem one_div_antitone : ∀ ⦃m n : ℕ⦄, 0 < m → m ≤ n → 1 / (n : ℝ) ≤ 1 / (m : ℝ) := by
  intro m n hm hmn
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.lt_of_lt_of_le hm hmn
  rw [div_le_div_iff hn' hm']
  simp only [one_mul]
  exact Nat.cast_le.mpr hmn

/-- The constant sequence 1 is not summable (Σ 1 = ∞). -/
theorem not_summable_one : ¬Summable (fun _ : ℕ => (1 : ℝ)) :=
  not_summable_const_of_ne_zero one_ne_zero

/-- The condensed harmonic series Σ 2^k/2^k = Σ 1 diverges. -/
theorem condensed_harmonic_diverges :
    ¬Summable (fun k : ℕ => (2 : ℝ) ^ k * (1 / (2 : ℝ) ^ k)) := by
  convert not_summable_one using 1
  ext k; field_simp

/-- Oresme's result via condensation: the harmonic series Σ 1/n diverges.
    This shows Oresme's grouping argument is a special case of Cauchy condensation. -/
theorem oresme_via_condensation : ¬Summable (fun n : ℕ => 1 / (n : ℝ)) := by
  rw [cauchy_condensation_diverges one_div_nonneg_nat one_div_antitone]
  convert condensed_harmonic_diverges using 1
  ext k; push_cast; ring

/-- Concordance: our result matches Mathlib's direct proof. -/
theorem harmonic_diverges_mathlib : ¬Summable (fun n : ℕ => (1 : ℝ) / n) :=
  not_summable_one_div_natCast

/-! ## Part III: Why This is a Complete Characterization

The condensation test fully characterizes summability for nonneg antitone sequences.
Any such sequence can be tested by computing its condensed series. This includes:
- Harmonic series: f(n) = 1/n → condensed = Σ 1 (diverges)
- p-series: f(n) = 1/n^p → condensed = Σ 2^(k(1-p)) (converges iff p > 1)
- Log-harmonic: f(n) = 1/(n log n) → condensed = �� 1/(k log 2) (diverges)
- Iterated log: f(n) = 1/(n log n (log log n)^p) → converges iff p > 1

The test reduces a potentially subtle convergence question to checking
a simpler geometric-type series. -/

/-- The characterization is an exact biconditional (not just sufficient condition). -/
theorem condensation_iff_summable {f : ℕ → ℝ}
    (hf_nonneg : ∀ n, 0 ≤ f n)
    (hf_anti : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m) :
    Summable f ↔ Summable (fun k => (2 : ℝ) ^ k * f (2 ^ k)) :=
  cauchy_condensation_test hf_nonneg hf_anti

end HarmonicDivergenceOQ04
