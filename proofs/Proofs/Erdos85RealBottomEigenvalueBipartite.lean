import Mathlib

/-!
# A real bottom eigenmode forces bipartiteness

This is the converse equality case needed by the exterior-pair spectral
dichotomy.  A nonzero real eigenvector at minus the regular degree has
constant absolute value and reverses sign along every edge.
-/

open SimpleGraph

namespace Erdos85

private theorem real_eq_lowerBound_of_sum_eq_card_mul
    {V : Type*} [DecidableEq V] (s : Finset V) (f : V → ℝ) (b : ℝ)
    (hbound : ∀ z ∈ s, b ≤ f z)
    (hsum : ∑ z ∈ s, f z = (s.card : ℝ) * b)
    {y : V} (hy : y ∈ s) : f y = b := by
  apply le_antisymm
  · by_contra hnot
    have hylt : b < f y := lt_of_not_ge hnot
    have hlt : ∑ _z ∈ s, b < ∑ z ∈ s, f z := by
      apply Finset.sum_lt_sum
      · exact hbound
      · exact ⟨y, hy, hylt⟩
    rw [Finset.sum_const, hsum] at hlt
    norm_num at hlt
  · exact hbound y hy

private theorem real_eq_upperBound_of_sum_eq_card_mul
    {V : Type*} [DecidableEq V] (s : Finset V) (f : V → ℝ) (b : ℝ)
    (hbound : ∀ z ∈ s, f z ≤ b)
    (hsum : ∑ z ∈ s, f z = (s.card : ℝ) * b)
    {y : V} (hy : y ∈ s) : f y = b := by
  apply le_antisymm (hbound y hy)
  by_contra hnot
  have hylt : f y < b := lt_of_not_ge hnot
  have hlt : ∑ z ∈ s, f z < ∑ _z ∈ s, b := by
    apply Finset.sum_lt_sum
    · exact hbound
    · exact ⟨y, hy, hylt⟩
  rw [Finset.sum_const, hsum] at hlt
  norm_num at hlt

private theorem reachable_induction_of_adj_closed
    {V : Type*} (D : SimpleGraph V) (P : V → Prop)
    (hP : ∀ x y, D.Adj x y → P x → P y) {u v : V}
    (h : D.Reachable u v) (hu : P u) : P v := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact hu
  | cons hadj _ ih => exact ih (hP _ _ hadj hu)

/-- Equality at the negative regular-degree bound makes a nonzero real mode
alternate across every edge. -/
theorem real_negativeDegree_eigenvector_constant_abs_and_edge_neg
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (hconn : D.Connected) (k : ℕ) (hreg : ∀ x, D.degree x = k)
    (w : V → ℝ) (hw : w ≠ 0)
    (heigen : ∀ x, ∑ y ∈ D.neighborFinset x, w y = -(k : ℝ) * w x) :
    ∃ amplitude : ℝ, 0 < amplitude ∧
      (∀ x, |w x| = amplitude) ∧
      (∀ x y, D.Adj x y → w y = -w x) := by
  letI : Nonempty V := hconn.nonempty
  obtain ⟨x₀, hx₀⟩ := Finite.exists_max (fun x => |w x|)
  let amplitude : ℝ := |w x₀|
  have hamp0 : 0 ≤ amplitude := abs_nonneg _
  have hmax : ∀ z, |w z| ≤ amplitude := hx₀
  have hflip : ∀ x y, D.Adj x y → |w x| = amplitude → w y = -w x := by
    intro x y hxy hxabs
    have hcard : (D.neighborFinset x).card = k := by
      rw [D.card_neighborFinset_eq_degree, hreg]
    have hyMem : y ∈ D.neighborFinset x :=
      (D.mem_neighborFinset x y).mpr hxy
    rcases (abs_eq hamp0).mp hxabs with hx | hx
    · have hsum : ∑ z ∈ D.neighborFinset x, w z =
          ((D.neighborFinset x).card : ℝ) * (-amplitude) := by
        rw [heigen x, hx, hcard]
        ring
      have hlower : ∀ z ∈ D.neighborFinset x, -amplitude ≤ w z := by
        intro z _
        exact (neg_le_neg (hmax z)).trans (neg_abs_le (w z))
      have hy := real_eq_lowerBound_of_sum_eq_card_mul
        (D.neighborFinset x) w (-amplitude) hlower hsum hyMem
      linarith
    · have hsum : ∑ z ∈ D.neighborFinset x, w z =
          ((D.neighborFinset x).card : ℝ) * amplitude := by
        rw [heigen x, hx, hcard]
        ring
      have hupper : ∀ z ∈ D.neighborFinset x, w z ≤ amplitude := by
        intro z _
        exact (le_abs_self (w z)).trans (hmax z)
      have hy := real_eq_upperBound_of_sum_eq_card_mul
        (D.neighborFinset x) w amplitude hupper hsum hyMem
      linarith
  have habs : ∀ x, |w x| = amplitude := by
    intro x
    apply reachable_induction_of_adj_closed D
      (fun z => |w z| = amplitude)
      (fun u v huv hu => by rw [hflip u v huv hu, abs_neg, hu])
      (hconn.preconnected x₀ x)
    rfl
  have hamp : 0 < amplitude := by
    apply lt_of_le_of_ne hamp0
    intro hz
    have hall : w = 0 := by
      funext x
      have hx : |w x| = 0 := (habs x).trans hz.symm
      simpa using (abs_eq_zero.mp hx)
    exact hw hall
  exact ⟨amplitude, hamp, habs, fun x y hxy => hflip x y hxy (habs x)⟩

/-- A connected regular graph admitting a nonzero real eigenvector at minus
its degree is bipartite. -/
theorem isBipartite_of_real_negativeDegree_eigenvector
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (hconn : D.Connected) (k : ℕ) (hreg : ∀ x, D.degree x = k)
    (w : V → ℝ) (hw : w ≠ 0)
    (heigen : ∀ x, ∑ y ∈ D.neighborFinset x, w y = -(k : ℝ) * w x) :
    D.IsBipartite := by
  obtain ⟨amplitude, hamp, habs, hflip⟩ :=
    real_negativeDegree_eigenvector_constant_abs_and_edge_neg
      D hconn k hreg w hw heigen
  let col : V → Fin 2 := fun x => finTwoEquiv.symm (decide (0 < w x))
  refine ⟨col, ?_⟩
  intro x y hxy heq
  have hbool : decide (0 < w x) = decide (0 < w y) :=
    finTwoEquiv.symm.injective heq
  have hxne : w x ≠ 0 := by
    intro hx
    have := habs x
    rw [hx, abs_zero] at this
    linarith
  rw [hflip x y hxy] at hbool
  by_cases hx : 0 < w x
  · have hn : ¬0 < -w x := by linarith
    simp [hx, hn] at hbool
  · have hxlt : w x < 0 := lt_of_le_of_ne (le_of_not_gt hx) hxne
    have hn : 0 < -w x := by linarith
    simp [hx, hn] at hbool

/-- Complex bottom modes reduce to a nonzero real or imaginary bottom mode. -/
theorem isBipartite_of_complex_negativeDegree_eigenvector
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (hconn : D.Connected) (k : ℕ) (hreg : ∀ x, D.degree x = k)
    (w : V → ℂ) (hw : w ≠ 0)
    (heigen : ∀ x, ∑ y ∈ D.neighborFinset x, w y = -(k : ℂ) * w x) :
    D.IsBipartite := by
  let wr : V → ℝ := fun x => (w x).re
  let wi : V → ℝ := fun x => (w x).im
  have hre : ∀ x, ∑ y ∈ D.neighborFinset x, wr y = -(k : ℝ) * wr x := by
    intro x
    have hx := congrArg Complex.re (heigen x)
    simpa [wr] using hx
  have him : ∀ x, ∑ y ∈ D.neighborFinset x, wi y = -(k : ℝ) * wi x := by
    intro x
    have hx := congrArg Complex.im (heigen x)
    simpa [wi] using hx
  by_cases hwr : wr = 0
  · have hwi : wi ≠ 0 := by
      intro hwi
      apply hw
      funext x
      apply Complex.ext
      · exact congrFun hwr x
      · exact congrFun hwi x
    exact isBipartite_of_real_negativeDegree_eigenvector
      D hconn k hreg wi hwi him
  · exact isBipartite_of_real_negativeDegree_eigenvector
      D hconn k hreg wr hwr hre

end Erdos85

#print axioms Erdos85.real_negativeDegree_eigenvector_constant_abs_and_edge_neg
#print axioms Erdos85.isBipartite_of_real_negativeDegree_eigenvector
#print axioms Erdos85.isBipartite_of_complex_negativeDegree_eigenvector
