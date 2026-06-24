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
  intro i j h
  simp only [Fin.mk.injEq] at h
  -- h : i·b ≡ j·b (mod a); coprimality lets us cancel the right factor b.
  have hmod : i.val * b ≡ j.val * b [MOD a] := h
  have hij : i.val ≡ j.val [MOD a] := Nat.ModEq.cancel_right_of_coprime hab hmod
  have heq : i.val % a = j.val % a := hij
  rw [Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] at heq
  exact Fin.ext heq

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
  simp only [frobeniusNumber] at hn_lt hxy hxy'
  -- Summing the two representations: a·X + b·Y = a·b with X = x+x'+1, Y = y+y'+1 ≥ 1.
  have hX1 : 1 ≤ x + x' + 1 := by omega
  have hY1 : 1 ≤ y + y' + 1 := by omega
  have hkey : a * (x + x' + 1) + b * (y + y' + 1) = a * b := by
    have e : a * (x + x' + 1) + b * (y + y' + 1)
        = (a * x + b * y) + (a * x' + b * y') + a + b := by ring
    rw [e, ← hxy, ← hxy']; omega
  -- a ∣ b·Y : b·Y = a·b − a·X is a multiple of a; coprimality lifts a ∣ b·Y to a ∣ Y.
  have hbY : b * (y + y' + 1) = a * b - a * (x + x' + 1) := by omega
  have hay : a ∣ b * (y + y' + 1) := by
    rw [hbY]; exact Nat.dvd_sub ⟨b, rfl⟩ ⟨x + x' + 1, rfl⟩
  have haX : a * (x + x' + 1) = a * b - b * (y + y' + 1) := by omega
  have hbx : b ∣ a * (x + x' + 1) := by
    rw [haX]; exact Nat.dvd_sub ⟨a, by ring⟩ ⟨y + y' + 1, rfl⟩
  -- Hence Y ≥ a and X ≥ b, forcing a·X + b·Y ≥ 2ab > ab.
  have hYa : a ≤ y + y' + 1 := Nat.le_of_dvd (by omega) (hab.dvd_of_dvd_mul_left hay)
  have hXb : b ≤ x + x' + 1 := Nat.le_of_dvd (by omega) (hab.symm.dvd_of_dvd_mul_left hbx)
  have hAX : a * b ≤ a * (x + x' + 1) := Nat.mul_le_mul (le_refl a) hXb
  have hBY : b * a ≤ b * (y + y' + 1) := Nat.mul_le_mul (le_refl b) hYa
  have hcomm : b * a = a * b := Nat.mul_comm b a
  omega

/-- For 0 < n < g, at least one of n and g-n is representable. -/
theorem one_of_pair_rep (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b)
    {n : ℕ} (hn_pos : 0 < n) (hn_lt : n < frobeniusNumber a b) :
    Representable a b n ∨ Representable a b (frobeniusNumber a b - n) := by
  have hge : a + b ≤ a * b := by nlinarith
  have ha_pos : 0 < a := by omega
  simp only [frobeniusNumber] at hn_lt ⊢
  obtain ⟨k, hk_lt, hk_mod⟩ := exists_kb_mod ha_pos hab (n % a) (Nat.mod_lt n ha_pos)
  -- hk_mod : k·b % a = n % a, i.e. k·b ≡ n (mod a).
  have hmod : k * b ≡ n [MOD a] := hk_mod
  have hcomm : k * b = b * k := Nat.mul_comm k b
  by_cases hle : k * b ≤ n
  · left
    -- a ∣ n − k·b, so n = a·q + b·k.
    obtain ⟨q, hq⟩ := (Nat.modEq_iff_dvd' hle).mp hmod
    exact ⟨q, k, by omega⟩
  · right
    push_neg at hle
    -- a ∣ k·b − n (a positive multiple of a since k·b > n).
    have h_div : a ∣ k * b - n := (Nat.modEq_iff_dvd' hle.le).mp hmod.symm
    have hkb_ge : a ≤ k * b - n := Nat.le_of_dvd (by omega) h_div
    have hk_bound : k ≤ a - 1 := by omega
    -- Nonlinear bookkeeping that `omega` cannot see on its own:
    --   b·(a−1−k) + b·k + b = a·b   (valid because k ≤ a−1).
    have hrel : b * (a - 1 - k) + b * k + b = a * b := by
      have hk' : (a - 1 - k) + k + 1 = a := by omega
      calc b * (a - 1 - k) + b * k + b
          = b * ((a - 1 - k) + k + 1) := by ring
        _ = b * a := by rw [hk']
        _ = a * b := Nat.mul_comm b a
    have hgn_lb : b * (a - 1 - k) ≤ a * b - a - b - n := by omega
    have h_div2 : a ∣ (a * b - a - b - n) - b * (a - 1 - k) := by
      have hid : (a * b - a - b - n) - b * (a - 1 - k) = k * b - n - a := by omega
      rw [hid]; exact Nat.dvd_sub h_div (dvd_refl a)
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
