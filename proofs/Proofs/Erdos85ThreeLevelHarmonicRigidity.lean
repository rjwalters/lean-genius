import Proofs.Erdos85ThreeLevelExtremalSum

/-! # Rigidity of three-level harmonic functions

A bounded discrete harmonic function on a connected regular graph is
constant.  This file packages the special integer-valued form used by the
binary square-order defect argument.
-/

open SimpleGraph

namespace Erdos85

private theorem reachable_induction_of_adj_closed_threeLevel
    {V : Type*} (D : SimpleGraph V) (P : V → Prop)
    (hP : ∀ x y, D.Adj x y → P x → P y) {u v : V}
    (h : D.Reachable u v) (hu : P u) : P v := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact hu
  | cons hadj _ ih => exact ih (hP _ _ hadj hu)

/-- A `{-2,0,2}`-valued harmonic function on a connected regular graph is
constant. -/
theorem threeLevel_harmonic_constant_of_connected_regular
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (hconn : D.Connected) (k : ℕ) (hreg : ∀ x, D.degree x = k)
    (e : V → ℤ)
    (hlevels : ∀ x, e x = -2 ∨ e x = 0 ∨ e x = 2)
    (hharm : ∀ x, ∑ y ∈ D.neighborFinset x, e y = (k : ℤ) * e x) :
    ∀ x y, e x = e y := by
  have hedge : ∀ x y, D.Adj x y → e x = e y := by
    intro x y hxy
    have hyMem : y ∈ D.neighborFinset x := (D.mem_neighborFinset x y).mpr hxy
    have hxMem : x ∈ D.neighborFinset y :=
      (D.mem_neighborFinset y x).mpr hxy.symm
    have hcard (z : V) : (D.neighborFinset z).card = k := by
      rw [D.card_neighborFinset_eq_degree, hreg]
    rcases hlevels x with hx | hx | hx
    · have hsum : ∑ z ∈ D.neighborFinset x, e z =
          -2 * ((D.neighborFinset x).card : ℤ) := by
        rw [hharm x, hx, hcard]
        ring
      exact hx.trans (eq_neg_two_of_threeLevel_sum_eq_neg_two_mul_card
        (D.neighborFinset x) e (fun z _ => hlevels z) hsum hyMem).symm
    · rcases hlevels y with hy | hy | hy
      · have hsum : ∑ z ∈ D.neighborFinset y, e z =
            -2 * ((D.neighborFinset y).card : ℤ) := by
          rw [hharm y, hy, hcard]
          ring
        have hxneg := eq_neg_two_of_threeLevel_sum_eq_neg_two_mul_card
          (D.neighborFinset y) e (fun z _ => hlevels z) hsum hxMem
        omega
      · exact hx.trans hy.symm
      · have hsum : ∑ z ∈ D.neighborFinset y, e z =
            2 * ((D.neighborFinset y).card : ℤ) := by
          rw [hharm y, hy, hcard]
          ring
        have hxtwo := eq_two_of_threeLevel_sum_eq_two_mul_card
          (D.neighborFinset y) e (fun z _ => hlevels z) hsum hxMem
        omega
    · have hsum : ∑ z ∈ D.neighborFinset x, e z =
          2 * ((D.neighborFinset x).card : ℤ) := by
        rw [hharm x, hx, hcard]
        ring
      exact hx.trans (eq_two_of_threeLevel_sum_eq_two_mul_card
        (D.neighborFinset x) e (fun z _ => hlevels z) hsum hyMem).symm
  intro x y
  exact reachable_induction_of_adj_closed_threeLevel D
    (fun z => e x = e z)
    (fun u v huv hu => hu.trans (hedge u v huv))
    (hconn.preconnected x y) rfl

end Erdos85

#print axioms Erdos85.threeLevel_harmonic_constant_of_connected_regular
