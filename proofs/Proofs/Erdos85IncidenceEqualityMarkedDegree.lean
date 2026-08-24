import Proofs.Erdos85IncidenceEqualitySupportClassification

/-!
# Marked degree in a minimum-energy incidence row

For the incidence bottleneck the marked diagonal coordinate is one less than
the triangle-free-edge degree.  Unit-entry classification therefore restricts
that degree to zero or two.
-/

open Finset BigOperators

namespace Erdos85

noncomputable section

theorem minimumEnergy_markedDegree_eq_zero_or_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (y : V → ℤ) {q : ℕ} (hq : 8 ≤ q)
    (hmlo : 2 ≤ (finiteVectorSupport y).card)
    (hmhi : (finiteVectorSupport y).card ≤ q)
    (hmul : (finiteVectorSupport y).card *
      (q - (finiteVectorSupport y).card + 1) ≤ 2 * q)
    (hsum : ∑ v, y v = 0)
    (henergy : ∑ v, y v ^ 2 = (q : ℤ))
    (hfour : 4 ∣ q) (x : V) (hodd : Odd (y x))
    (t : ℕ) (hdiag : y x = (t : ℤ) - 1) :
    t = 0 ∨ t = 2 := by
  have hyx : y x ≠ 0 := by
    obtain ⟨k, hk⟩ := hodd
    omega
  have hunit := minimumEnergy_apply_eq_one_or_neg_one
    y hq hmlo hmhi hmul hsum henergy hfour x hodd x hyx
  rcases hunit with hpos | hneg <;> rw [hdiag] at * <;> omega

end

end Erdos85

#print axioms Erdos85.minimumEnergy_markedDegree_eq_zero_or_two
