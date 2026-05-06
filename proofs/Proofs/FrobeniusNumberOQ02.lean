/-
  OQ-02: Symmetry of Representable Numbers (Frobenius)
  (frobenius-number-oq-02)

  For coprime a, b ≥ 2 with Frobenius number g = ab-a-b, and 0 < n < g:
    Representable a b n ↔ ¬Representable a b (g - n)

  Note: The problem JSON statement "¬Rep(n) ↔ ¬Rep(g-n)" is INCORRECT.
  The correct symmetry pairs each representable with a non-representable:
  For a=3, b=5, g=7: n=1 is non-rep, g-n=6 is representable.

  ## Status: 0 sorries, 0 axioms (uses exists_mul_mod helper reproved here)
-/
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic
import Proofs.FrobeniusNumber

namespace FrobeniusSymmetry

open FrobeniusNumber

variable {a b : ℕ}

/-! ## Helper: every residue mod a is represented as k*b -/

private lemma mul_mod_inj (ha : 0 < a) (hab : Nat.Coprime a b) :
    Function.Injective (fun k : Fin a => (⟨k.val * b % a, Nat.mod_lt _ ha⟩ : Fin a)) := by
  intro ⟨i, hi⟩ ⟨j, hj⟩ h
  simp only [Fin.mk.injEq] at h
  -- i*b ≡ j*b (mod a) → a | (i-j)*b → a | i-j → i = j
  have key : (i : ZMod a) * b = (j : ZMod a) * b := by
    ext; simp [ZMod.val_natCast, h]
  have hb_unit : IsUnit ((b : ℕ) : ZMod a) := by
    rw [ZMod.isUnit_natCast_iff]; exact hab.symm
  have hij : (i : ZMod a) = (j : ZMod a) :=
    mul_right_cancel₀ (IsUnit.ne_zero hb_unit) key
  have := ZMod.natCast_zmod_eq_zero_iff_dvd (i + a - j) a |>.mpr
  simp [ZMod.natCast_self_eq_zero, ← hij] at this
  omega

private lemma exists_kb_mod (ha : 0 < a) (hab : Nat.Coprime a b) (r : ℕ) (hr : r < a) :
    ∃ k < a, k * b % a = r := by
  have hsurj := Finite.injective_iff_surjective.mp (mul_mod_inj ha hab)
  obtain ⟨⟨k, hk⟩, hkr⟩ := hsurj ⟨r, hr⟩
  simp only [Fin.mk.injEq] at hkr
  exact ⟨k, hk, hkr⟩

/-! ## Main results -/

/-- If n and g-n are both representable, contradiction. -/
theorem rep_and_complement_false (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b)
    {n : ℕ} (hn_pos : 0 < n) (hn_lt : n < frobeniusNumber a b)
    (hn : Representable a b n) (hgn : Representable a b (frobeniusNumber a b - n)) : False := by
  obtain ⟨x, y, hxy⟩ := hn; obtain ⟨x', y', hxy'⟩ := hgn
  have hge : a + b ≤ a * b := by nlinarith
  have hkey : a * b = a * (x + x' + 1) + b * (y + y' + 1) := by
    simp only [frobeniusNumber] at hn_lt hxy hxy'; omega
  have hx1b : x + x' + 1 ≤ b := by nlinarith [Nat.zero_le (b * (y + y' + 1))]
  have hy1a : y + y' + 1 ≤ a := by nlinarith [Nat.zero_le (a * (x + x' + 1))]
  have hay : a ∣ b * (y + y' + 1) := ⟨b - (x + x' + 1), by omega⟩
  have hbx : b ∣ a * (x + x' + 1) := ⟨a - (y + y' + 1), by omega⟩
  linarith [Nat.mul_le_mul_left a (Nat.le_of_dvd (by omega) (hab.symm.dvd_of_dvd_mul_left hbx)),
            Nat.mul_le_mul_left b (Nat.le_of_dvd (by omega) (hab.dvd_of_dvd_mul_left hay))]

/-- For 0 < n < g, at least one of n and g-n is representable. -/
theorem one_of_pair_rep (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b)
    {n : ℕ} (hn_pos : 0 < n) (hn_lt : n < frobeniusNumber a b) :
    Representable a b n ∨ Representable a b (frobeniusNumber a b - n) := by
  have hge : a + b ≤ a * b := by nlinarith
  have ha_pos : 0 < a := by omega
  simp only [frobeniusNumber] at hn_lt ⊢
  obtain ⟨k, hk_lt, hk_mod⟩ := exists_kb_mod ha_pos hab (n % a) (Nat.mod_lt n ha_pos)
  by_cases hle : k * b ≤ n
  · left
    obtain ⟨q, hq⟩ := (Nat.dvd_iff_mod_eq_zero.mpr (by omega) : a ∣ n - k * b)
    exact ⟨q, k, by omega⟩
  · right
    push_neg at hle
    have h_div : a ∣ k * b - n := Nat.dvd_iff_mod_eq_zero.mpr (by omega)
    have hkb_ge : a ≤ k * b - n := Nat.le_of_dvd (by omega) h_div
    have hk_bound : k ≤ a - 1 := by omega
    have hgn_lb : b * (a - 1 - k) ≤ a * b - a - b - n := by
      nlinarith [Nat.mul_le_mul_right b hk_bound]
    have h_div2 : a ∣ (a * b - a - b - n) - b * (a - 1 - k) := by
      have : (a * b - a - b - n) - b * (a - 1 - k) = k * b - n - a := by omega
      rw [this]; exact Nat.dvd_sub' h_div (dvd_refl a)
    obtain ⟨q, hq⟩ := h_div2
    exact ⟨q, a - 1 - k, by omega⟩

/-- **Frobenius Symmetry**: Rep(n) ↔ ¬Rep(g-n) for 0 < n < g. -/
theorem frobenius_symmetry (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b)
    {n : ℕ} (hn_pos : 0 < n) (hn_lt : n < frobeniusNumber a b) :
    Representable a b n ↔ ¬Representable a b (frobeniusNumber a b - n) := by
  constructor
  · intro hrep hgn; exact rep_and_complement_false ha hb hab hn_pos hn_lt hrep hgn
  · intro hnotgn
    rcases one_of_pair_rep ha hb hab hn_pos hn_lt with h | h
    · exact h
    · exact absurd h hnotgn

end FrobeniusSymmetry
