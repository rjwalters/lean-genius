/-
# Erdős #395 OQ-01 Incomplete-01: Proving the Carnielli-Carolino Counterexample

**Problem** (erdos-395-oq-01-incomplete-01):
Prove `counterexample_always_large` without axioms:
For the Carnielli-Carolino configuration z₁=1, zₖ=i (k≥2, n even, n≥2),
every sign vector ε gives |ε₁z₁ + ... + εₙzₙ| ≥ √2.

## Key Insight

For z = (1, i, i, ..., i) and sign vector ε:
  S = ε₀ + (ε₁ + ... + εₙ₋₁)·i
  |S|² = ε₀² + T²  where T = ε₁ + ... + εₙ₋₁

Since n is even, n-1 is odd. In ZMod 2, each εⱼ ≡ 1 (mod 2), so T ≡ n-1 ≡ 1 (mod 2).
T is odd → T ≠ 0 (integer) → T² ≥ 1 → |S|² = 1 + T² ≥ 2 → |S| ≥ √2.

## Axioms: 0  |  Sorries: 0  |  Theorems: 3
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Proofs.Erdos395Problem

open scoped Classical

open Complex Erdos395 Real Finset

namespace Erdos395OQ01Incomplete01

-- ============================================================
-- SECTION I: Helpers
-- ============================================================

/-- Real part of the signed sum on the counterexample is ε₀. -/
private lemma cc_re (n : ℕ) (hn2 : n ≥ 2) (hn : Even n) (ε : Fin n → ℤ) :
    (signedSum (carnielli_carolino_counterexample n hn hn2) ε).re = ε ⟨0, by omega⟩ := by
  simp only [signedSum, carnielli_carolino_counterexample, Complex.re_sum]
  rw [← Finset.add_sum_erase (Finset.univ : Finset (Fin n))
      (fun i => (↑(ε i) * if i.val = 0 then (1 : ℂ) else I).re)
      (Finset.mem_univ (⟨0, by omega⟩ : Fin n))]
  have hzero : ∑ i ∈ (univ : Finset (Fin n)).erase ⟨0, by omega⟩,
      (↑(ε i) * if i.val = 0 then (1 : ℂ) else I).re = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hiv : i.val ≠ 0 := fun h => (Finset.mem_erase.mp hi).1 (Fin.ext h)
    simp [Complex.mul_re, hiv]
  rw [hzero, add_zero]
  simp

/-- Imaginary part of the signed sum on the counterexample is the tail sum cast to ℝ. -/
private lemma cc_im (n : ℕ) (hn2 : n ≥ 2) (hn : Even n) (ε : Fin n → ℤ) :
    (signedSum (carnielli_carolino_counterexample n hn hn2) ε).im =
    ↑(∑ i ∈ (univ : Finset (Fin n)).erase ⟨0, by omega⟩, ε i) := by
  simp only [signedSum, carnielli_carolino_counterexample, Complex.im_sum]
  simp only [Complex.mul_im, intCast_re, intCast_im, apply_ite Complex.im,
    I_re, I_im, mul_zero, add_zero, mul_one, mul_ite]
  -- Goal: ∑ i : Fin n, if i.val = 0 then 0 else (ε i : ℝ) = ↑(∑ i ∈ erase 0, ε i)
  -- Show LHS = ∑ i ∈ erase 0, (ε i : ℝ) by removing the zero term at i=0
  rw [show (∑ i : Fin n, if i.val = 0 then (0 : ℝ) else (ε i : ℝ)) =
      ∑ i ∈ (univ : Finset (Fin n)).erase ⟨0, by omega⟩, (ε i : ℝ) from by
    rw [← Finset.add_sum_erase (Finset.univ : Finset (Fin n))
        (fun i => if i.val = 0 then (0 : ℝ) else (ε i : ℝ))
        (Finset.mem_univ (⟨0, by omega⟩ : Fin n))]
    simp only [ite_true, zero_add]
    apply Finset.sum_congr rfl
    intro i hi
    simp [show i.val ≠ 0 from fun h => (Finset.mem_erase.mp hi).1 (Fin.ext h)]]
  push_cast [map_sum]
  rfl

/-- The tail sum T = ε₁+...+εₙ₋₁ is nonzero (parity argument). -/
private lemma tail_nonzero (n : ℕ) (hn2 : n ≥ 2) (hn : Even n)
    (ε : Fin n → ℤ) (hε : isSignVector ε) :
    (∑ i ∈ (univ : Finset (Fin n)).erase ⟨0, by omega⟩, ε i) ≠ 0 := by
  intro hz
  have hzero : ((∑ i ∈ (univ : Finset (Fin n)).erase ⟨0, by omega⟩, ε i : ℤ) : ZMod 2) = 0 :=
    by rw [hz]; simp
  have hone : ((∑ i ∈ (univ : Finset (Fin n)).erase ⟨0, by omega⟩, ε i : ℤ) : ZMod 2) = 1 := by
    push_cast [map_sum]
    have each : ∀ i ∈ (univ : Finset (Fin n)).erase ⟨0, by omega⟩, (ε i : ZMod 2) = 1 := by
      intro i _; rcases hε i with h | h <;> simp [h]
    rw [Finset.sum_congr rfl each, Finset.sum_const,
        Finset.card_erase_of_mem (mem_univ _), Finset.card_fin,
        nsmul_eq_mul, mul_one]
    obtain ⟨k, hk⟩ := hn
    have hk1 : k ≥ 1 := by omega
    have heq : n - 1 = 2 * (k - 1) + 1 := by omega
    rw [heq]; push_cast; simp [show (2 : ZMod 2) = 0 from by decide]
  exact one_ne_zero (hone ▸ hzero)

-- ============================================================
-- SECTION II: Main Theorem
-- ============================================================

/-- **Axiom-free proof** of `counterexample_always_large`:
    the Carnielli-Carolino configuration always gives |sum| ≥ √2. -/
theorem counterexample_always_large_proved
    (n : ℕ) (hn : Even n) (hn2 : n ≥ 2)
    (ε : Fin n → ℤ) (hε : isSignVector ε) :
    signedSumAbs (carnielli_carolino_counterexample n hn hn2) ε ≥ Real.sqrt 2 := by
  unfold signedSumAbs Complex.abs
  rw [Complex.norm_def]
  apply Real.sqrt_le_sqrt
  rw [Complex.normSq_apply, cc_re n hn2 hn, cc_im n hn2 hn]
  have he0 : ((ε ⟨0, by omega⟩ : ℤ) : ℝ) ^ 2 = 1 := by
    rcases hε ⟨0, by omega⟩ with h | h <;> simp [h]
  set T := ∑ i ∈ (univ : Finset (Fin n)).erase ⟨0, by omega⟩, ε i with hT_def
  have hT : T ≠ 0 := tail_nonzero n hn2 hn ε hε
  have hT_sq : (1 : ℝ) ≤ (T : ℝ) ^ 2 := by
    rcases (by omega : T ≤ -1 ∨ 1 ≤ T) with h | h
    · have : (T : ℝ) ≤ -1 := by exact_mod_cast h
      nlinarith
    · have : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast h
      nlinarith
  linarith

end Erdos395OQ01Incomplete01
