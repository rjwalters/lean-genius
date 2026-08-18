import Mathlib

/-! # Rigidity at the negative degree eigenvalue

An eigenvector of a connected regular graph at the negative of its degree
has constant absolute value and changes sign across every edge.  This is the
elementary equality case behind the usual bipartiteness criterion.
-/

open SimpleGraph

namespace Erdos85

private theorem eq_lowerBound_of_sum_eq_card_mul
    {V : Type*} [DecidableEq V] (s : Finset V) (f : V → ℤ) (b : ℤ)
    (hbound : ∀ z ∈ s, b ≤ f z)
    (hsum : ∑ z ∈ s, f z = (s.card : ℤ) * b)
    {y : V} (hy : y ∈ s) : f y = b := by
  apply le_antisymm
  · by_contra hnot
    have hylt : b < f y := lt_of_not_ge hnot
    have hlt : ∑ _z ∈ s, b < ∑ z ∈ s, f z := by
      apply Finset.sum_lt_sum
      · exact hbound
      · exact ⟨y, hy, hylt⟩
    rw [Finset.sum_const, hsum] at hlt
    simp at hlt
  · exact hbound y hy

private theorem eq_upperBound_of_sum_eq_card_mul
    {V : Type*} [DecidableEq V] (s : Finset V) (f : V → ℤ) (b : ℤ)
    (hbound : ∀ z ∈ s, f z ≤ b)
    (hsum : ∑ z ∈ s, f z = (s.card : ℤ) * b)
    {y : V} (hy : y ∈ s) : f y = b := by
  apply le_antisymm (hbound y hy)
  by_contra hnot
  have hylt : f y < b := lt_of_not_ge hnot
  have hlt : ∑ z ∈ s, f z < ∑ _z ∈ s, b := by
    apply Finset.sum_lt_sum
    · exact hbound
    · exact ⟨y, hy, hylt⟩
  rw [Finset.sum_const, hsum] at hlt
  simp at hlt

private theorem reachable_induction_of_adj_closed_negDegree
    {V : Type*} (D : SimpleGraph V) (P : V → Prop)
    (hP : ∀ x y, D.Adj x y → P x → P y) {u v : V}
    (h : D.Reachable u v) (hu : P u) : P v := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact hu
  | cons hadj _ ih => exact ih (hP _ _ hadj hu)

/-- A negative-degree eigenvector on a finite connected regular graph has a
constant nonnegative amplitude and reverses sign across every edge. -/
theorem negativeDegree_harmonic_constant_abs_and_edge_neg
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (hconn : D.Connected) (k : ℕ) (hreg : ∀ x, D.degree x = k)
    (w : V → ℤ)
    (heigen : ∀ x, ∑ y ∈ D.neighborFinset x, w y = -(k : ℤ) * w x) :
    ∃ amplitude : ℤ, 0 ≤ amplitude ∧
      (∀ x, |w x| = amplitude) ∧
      (∀ x y, D.Adj x y → w y = -w x) := by
  letI : Nonempty V := hconn.nonempty
  obtain ⟨x₀, hx₀⟩ := Finite.exists_max (fun x => |w x|)
  let amplitude : ℤ := |w x₀|
  have hamp : 0 ≤ amplitude := abs_nonneg _
  have hmax : ∀ z, |w z| ≤ amplitude := hx₀
  have hflip : ∀ x y, D.Adj x y → |w x| = amplitude → w y = -w x := by
    intro x y hxy hxabs
    have hcard : (D.neighborFinset x).card = k := by
      rw [D.card_neighborFinset_eq_degree, hreg]
    have hyMem : y ∈ D.neighborFinset x :=
      (D.mem_neighborFinset x y).mpr hxy
    rcases (abs_eq hamp).mp hxabs with hx | hx
    · have hsum : ∑ z ∈ D.neighborFinset x, w z =
          ((D.neighborFinset x).card : ℤ) * (-amplitude) := by
        rw [heigen x, hx, hcard]
        ring
      have hlower : ∀ z ∈ D.neighborFinset x, -amplitude ≤ w z := by
        intro z _
        have := hmax z
        omega
      have hy := eq_lowerBound_of_sum_eq_card_mul
        (D.neighborFinset x) w (-amplitude) hlower hsum hyMem
      omega
    · have hsum : ∑ z ∈ D.neighborFinset x, w z =
          ((D.neighborFinset x).card : ℤ) * amplitude := by
        rw [heigen x, hx, hcard]
        ring
      have hupper : ∀ z ∈ D.neighborFinset x, w z ≤ amplitude := by
        intro z _
        have := hmax z
        omega
      have hy := eq_upperBound_of_sum_eq_card_mul
        (D.neighborFinset x) w amplitude hupper hsum hyMem
      omega
  have habs : ∀ x, |w x| = amplitude := by
    intro x
    apply reachable_induction_of_adj_closed_negDegree D
      (fun z => |w z| = amplitude)
      (fun u v huv hu => by rw [hflip u v huv hu, abs_neg, hu])
      (hconn.preconnected x₀ x)
    rfl
  exact ⟨amplitude, hamp, habs, fun x y hxy => hflip x y hxy (habs x)⟩

end Erdos85

#print axioms Erdos85.negativeDegree_harmonic_constant_abs_and_edge_neg
