import Proofs.Erdos85IncidenceEqualitySupportArithmetic
import Proofs.Erdos85IncidenceEqualityBalancedSupport
import Proofs.Erdos85IncidenceEqualitySupportTwoParity

/-!
# Classification of minimum-energy incidence rows

The support sandwich leaves sizes `2`, `q-1`, and `q`.  Four-divisible
energy plus an odd marked coordinate excludes size two; integer square
arithmetic excludes `q-1`.  Thus the support has size `q`, all entries are
signed units, and zero sum balances the two signs.
-/

open Finset BigOperators

namespace Erdos85

noncomputable section

/-- Abstract minimum-energy classification in the exact interface supplied
by the graph support bounds. -/
theorem minimumEnergy_support_eq_self_and_balanced
    {V : Type*} [Fintype V] [DecidableEq V]
    (y : V → ℤ) {q : ℕ} (hq : 8 ≤ q)
    (hmlo : 2 ≤ (finiteVectorSupport y).card)
    (hmhi : (finiteVectorSupport y).card ≤ q)
    (hmul : (finiteVectorSupport y).card *
      (q - (finiteVectorSupport y).card + 1) ≤ 2 * q)
    (hsum : ∑ v, y v = 0)
    (henergy : ∑ v, y v ^ 2 = (q : ℤ))
    (hfour : 4 ∣ q) (x : V) (hodd : Odd (y x)) :
    (finiteVectorSupport y).card = q ∧
      2 * (Finset.univ.filter fun v => y v = 1).card = q ∧
      2 * (Finset.univ.filter fun v => y v = -1).card = q := by
  have hcases := support_card_eq_two_or_pred_or_self_of_mul_le_two_mul
    hq hmlo hmhi hmul
  have hneTwo : (finiteVectorSupport y).card ≠ 2 :=
    support_card_ne_two_of_sum_zero_of_four_dvd_sq_sum_of_odd_apply
      y hsum henergy hfour x hodd
  have hnePred : (finiteVectorSupport y).card ≠ q - 1 := by
    simpa [finiteVectorSupport] using
      (finiteSupport_card_ne_pred_of_sum_sq_eq y (by omega) henergy)
  rcases hcases with htwo | hpred | hself
  · exact False.elim (hneTwo htwo)
  · exact False.elim (hnePred hpred)
  · refine ⟨hself, ?_⟩
    exact balanced_sign_card_of_support_card_eq_energy_of_sum_eq_zero
      y (by simpa [finiteVectorSupport] using hself) henergy hsum

/-- Coordinate form: every nonzero entry in the classified minimum-energy
row is `+1` or `-1`. -/
theorem minimumEnergy_apply_eq_one_or_neg_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (y : V → ℤ) {q : ℕ} (hq : 8 ≤ q)
    (hmlo : 2 ≤ (finiteVectorSupport y).card)
    (hmhi : (finiteVectorSupport y).card ≤ q)
    (hmul : (finiteVectorSupport y).card *
      (q - (finiteVectorSupport y).card + 1) ≤ 2 * q)
    (hsum : ∑ v, y v = 0)
    (henergy : ∑ v, y v ^ 2 = (q : ℤ))
    (hfour : 4 ∣ q) (x : V) (hodd : Odd (y x))
    (v : V) (hv : y v ≠ 0) :
    y v = 1 ∨ y v = -1 := by
  have hclass := minimumEnergy_support_eq_self_and_balanced
    y hq hmlo hmhi hmul hsum henergy hfour x hodd
  apply forall_eq_one_or_neg_one_of_support_card_eq_sum_sq y
  rw [henergy]
  exact_mod_cast hclass.1.symm
  exact hv

/-- A zero-sum integer vector bounded below by `-1` cannot have support two
and square energy at least eight.  At support two its two nonzero entries
are opposites; the lower bound on both therefore traps them at `1` and
`-1`, whose total square energy is only two. -/
theorem support_card_ne_two_of_sum_zero_of_neg_one_le_of_four_dvd_sq_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (y : V → ℤ) (hlower : ∀ v, (-1 : ℤ) ≤ y v)
    (hsum : ∑ v, y v = 0) {q : ℕ}
    (henergy : ∑ v, y v ^ 2 = (q : ℤ)) (hfour : 4 ∣ q) :
    (finiteVectorSupport y).card ≠ 2 := by
  intro hcard
  have heven : ∀ v, Even (y v) :=
    even_apply_of_support_card_two_of_sum_zero_of_four_dvd_sq_sum
      y hcard hsum henergy hfour
  have hnonneg : ∀ v, 0 ≤ y v := by
    intro v
    obtain ⟨a, ha⟩ := heven v
    have hl := hlower v
    rw [ha] at hl ⊢
    omega
  have hyzero : y = 0 := by
    funext v
    have hvle : y v ≤ 0 := by
      by_contra hv
      have hvpos : 0 < y v := lt_of_not_ge hv
      have hsumOther : 0 ≤ ∑ w ∈ Finset.univ.erase v, y w :=
        Finset.sum_nonneg fun w _ => hnonneg w
      have hsplit := Finset.sum_erase_add Finset.univ y (Finset.mem_univ v)
      rw [hsum] at hsplit
      omega
    exact le_antisymm hvle (hnonneg v)
  subst y
  simp [finiteVectorSupport] at hcard

/-- Endpoint form of the minimum-energy support classification.  The
occupancy deviation `y=r-1` is automatically bounded below by `-1`; this
rules out the two-coordinate escape without needing an odd marked entry.
Consequently the support has size `q`, and exactly half of its coordinates
are `1` and half are `-1`. -/
theorem minimumEnergy_support_eq_self_and_balanced_of_neg_one_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (y : V → ℤ) {q : ℕ} (hq : 8 ≤ q)
    (hmlo : 2 ≤ (finiteVectorSupport y).card)
    (hmhi : (finiteVectorSupport y).card ≤ q)
    (hmul : (finiteVectorSupport y).card *
      (q - (finiteVectorSupport y).card + 1) ≤ 2 * q)
    (hsum : ∑ v, y v = 0)
    (henergy : ∑ v, y v ^ 2 = (q : ℤ))
    (hfour : 4 ∣ q)
    (hlower : ∀ v, (-1 : ℤ) ≤ y v) :
    (finiteVectorSupport y).card = q ∧
      2 * (Finset.univ.filter fun v => y v = 1).card = q ∧
      2 * (Finset.univ.filter fun v => y v = -1).card = q := by
  have hcases := support_card_eq_two_or_pred_or_self_of_mul_le_two_mul
    hq hmlo hmhi hmul
  have hneTwo :=
    support_card_ne_two_of_sum_zero_of_neg_one_le_of_four_dvd_sq_sum
      y hlower hsum henergy hfour
  have hnePred : (finiteVectorSupport y).card ≠ q - 1 := by
    simpa [finiteVectorSupport] using
      (finiteSupport_card_ne_pred_of_sum_sq_eq y (by omega) henergy)
  rcases hcases with htwo | hpred | hself
  · exact False.elim (hneTwo htwo)
  · exact False.elim (hnePred hpred)
  · refine ⟨hself, ?_⟩
    exact balanced_sign_card_of_support_card_eq_energy_of_sum_eq_zero
      y (by simpa [finiteVectorSupport] using hself) henergy hsum

end

end Erdos85

#print axioms Erdos85.minimumEnergy_support_eq_self_and_balanced
#print axioms Erdos85.minimumEnergy_apply_eq_one_or_neg_one
#print axioms Erdos85.support_card_ne_two_of_sum_zero_of_neg_one_le_of_four_dvd_sq_sum
#print axioms Erdos85.minimumEnergy_support_eq_self_and_balanced_of_neg_one_le
