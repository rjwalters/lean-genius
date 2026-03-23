/-
  Aristotle targets for Roth's Theorem (roth-theorem-k3)
  Routine supporting lemmas for automated proof search.
  See RothTheorem.lean for the main formalization.

  All sorries proved by researcher-3 (2026-03-22).
-/
import Mathlib

namespace Szemeredi.Roth.Aristotle

noncomputable def fourierCoeff {N : ℕ} (A : Finset (ZMod N)) (r : ZMod N) : ℂ :=
  A.sum fun x => Complex.exp (2 * Real.pi * Complex.I * (↑(ZMod.val (r * x)) / ↑N))

/-- Each exponential term has norm 1 (lies on the unit circle). -/
theorem exp_term_norm_one {N : ℕ} (r x : ZMod N) :
    ‖Complex.exp (2 * Real.pi * Complex.I * (↑(ZMod.val (r * x)) / ↑N))‖ = 1 := by
  have hpure : (2 * ↑Real.pi * Complex.I * (↑(ZMod.val (r * x)) / ↑N)).re = 0 := by
    simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  simp [Complex.norm_exp, hpure]

/-- The Fourier coefficient at r is bounded by |A| (triangle inequality). -/
theorem fourierCoeff_norm_le {N : ℕ} (A : Finset (ZMod N)) (r : ZMod N) :
    ‖fourierCoeff A r‖ ≤ A.card := by
  unfold fourierCoeff
  calc ‖A.sum fun x => Complex.exp _‖
      ≤ A.sum fun x => ‖Complex.exp (2 * ↑Real.pi * Complex.I *
          (↑(ZMod.val (r * x)) / ↑N))‖ := norm_sum_le _ _
    _ = A.sum fun _ => (1 : ℝ) := by congr 1; ext x; exact exp_term_norm_one r x
    _ = A.card := by simp

/-- Cardinality of any subset of ZMod N is at most N. -/
theorem card_le_zmod {N : ℕ} [NeZero N] (A : Finset (ZMod N)) :
    A.card ≤ N := by
  calc A.card ≤ Finset.univ.card := Finset.card_le_card (Finset.subset_univ _)
    _ = N := by simp [ZMod.card]

/-- Cardinality bound in ℝ. -/
theorem card_le_zmod_real {N : ℕ} [NeZero N] (A : Finset (ZMod N)) :
    (A.card : ℝ) ≤ (N : ℝ) := by
  exact_mod_cast card_le_zmod A

/-- If a + d = a then d = 0 in any additive group. -/
theorem add_right_eq_self {G : Type*} [AddGroup G] (a d : G) :
    a + d = a → d = 0 := by
  intro h
  have : a + d = a + 0 := by rwa [add_zero]
  exact add_left_cancel this

/-- In ZMod N with N ≥ 2, there exist distinct elements. -/
theorem zmod_nontrivial {N : ℕ} (hN : 2 ≤ N) :
    ∃ a b : ZMod N, a ≠ b := by
  haveI : NeZero N := ⟨by omega⟩
  have : Nontrivial (ZMod N) := by
    rw [← Fintype.one_lt_card_iff_nontrivial, ZMod.card]; omega
  obtain ⟨a, b, h⟩ := this.exists_pair_ne
  exact ⟨a, b, h⟩

end Szemeredi.Roth.Aristotle
