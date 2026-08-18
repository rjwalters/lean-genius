import Mathlib

/-! # Integer harmonic rigidity on finite regular graphs

A harmonic function on a finite connected regular graph is constant.  This
maximum-principle form has no restriction on the range of the function and is
the q-generic kernel needed by the defect-component arguments.
-/

open SimpleGraph

namespace Erdos85

private theorem reachable_induction_of_adj_closed
    {V : Type*} (D : SimpleGraph V) (P : V → Prop)
    (hP : ∀ x y, D.Adj x y → P x → P y) {u v : V}
    (h : D.Reachable u v) (hu : P u) : P v := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact hu
  | cons hadj _ ih => exact ih (hP _ _ hadj hu)

/-- Every integer-valued harmonic function on a finite connected regular
graph is constant. -/
theorem integer_harmonic_constant_of_connected_regular
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (hconn : D.Connected) (k : ℕ) (hreg : ∀ x, D.degree x = k)
    (e : V → ℤ)
    (hharm : ∀ x, ∑ y ∈ D.neighborFinset x, e y = (k : ℤ) * e x) :
    ∀ x y, e x = e y := by
  letI : Nonempty V := hconn.nonempty
  obtain ⟨x₀, hx₀⟩ := Finite.exists_max e
  have hedge : ∀ x y, D.Adj x y → e x = e x₀ → e y = e x₀ := by
    intro x y hxy hx
    apply le_antisymm (hx₀ y)
    by_contra hnot
    have hylt : e y < e x₀ := lt_of_not_ge hnot
    have hsumlt :
        ∑ z ∈ D.neighborFinset x, e z <
          ∑ _z ∈ D.neighborFinset x, e x₀ := by
      apply Finset.sum_lt_sum
      · intro z _
        exact hx₀ z
      · exact ⟨y, (D.mem_neighborFinset x y).mpr hxy, hylt⟩
    have hcard : (D.neighborFinset x).card = k := by
      rw [D.card_neighborFinset_eq_degree, hreg]
    rw [hharm x, hx, Finset.sum_const, hcard] at hsumlt
    simp at hsumlt
  intro x y
  have hx : e x₀ = e x :=
    reachable_induction_of_adj_closed D (fun z => e x₀ = e z)
      (fun u v huv hu => (hedge u v huv hu.symm).symm)
      (hconn.preconnected x₀ x) rfl
  have hy : e x₀ = e y :=
    reachable_induction_of_adj_closed D (fun z => e x₀ = e z)
      (fun u v huv hu => (hedge u v huv hu.symm).symm)
      (hconn.preconnected x₀ y) rfl
  exact hx.symm.trans hy

end Erdos85

#print axioms Erdos85.integer_harmonic_constant_of_connected_regular
