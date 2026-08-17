import Mathlib

/-! # Six-coordinate normalization for codegree-four pairs -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- In a seven-regular graph, a pair with four common neighbors has three
private neighbors on each side. -/
theorem sevenRegular_codegreeFour_privateTriple_normalization
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (hreg : ∀ v, D.degree v = 7)
    {x y : V}
    (hcommon : (D.neighborFinset x ∩ D.neighborFinset y).card = 4) :
    ∃ P Q : Finset V,
      P.card = 3 ∧ Q.card = 3 ∧
      P = D.neighborFinset x \ D.neighborFinset y ∧
      Q = D.neighborFinset y \ D.neighborFinset x ∧
      Disjoint P Q ∧
      ∀ z : V, z ∉ P → z ∉ Q → (D.Adj x z ↔ D.Adj y z) := by
  let P := D.neighborFinset x \ D.neighborFinset y
  let Q := D.neighborFinset y \ D.neighborFinset x
  have hxcard : (D.neighborFinset x).card = 7 := by
    rw [D.card_neighborFinset_eq_degree, hreg x]
  have hycard : (D.neighborFinset y).card = 7 := by
    rw [D.card_neighborFinset_eq_degree, hreg y]
  have hcommon' : (D.neighborFinset y ∩ D.neighborFinset x).card = 4 := by
    simpa [Finset.inter_comm] using hcommon
  have hPcard : P.card = 3 := by
    dsimp [P]
    rw [Finset.card_sdiff, hcommon', hxcard]
  have hQcard : Q.card = 3 := by
    dsimp [Q]
    rw [Finset.card_sdiff, hcommon, hycard]
  have hdisj : Disjoint P Q := by
    rw [Finset.disjoint_left]
    intro z hzP hzQ
    have hzP' := Finset.mem_sdiff.mp hzP
    have hzQ' := Finset.mem_sdiff.mp hzQ
    exact hzP'.2 hzQ'.1
  refine ⟨P, Q, hPcard, hQcard, rfl, rfl, hdisj, ?_⟩
  intro z hzP hzQ
  rw [← D.mem_neighborFinset, ← D.mem_neighborFinset]
  constructor
  · intro hxz
    by_contra hyz
    exact hzP (Finset.mem_sdiff.mpr ⟨hxz, hyz⟩)
  · intro hyz
    by_contra hxz
    exact hzQ (Finset.mem_sdiff.mpr ⟨hyz, hxz⟩)

/-- The symmetric row-difference support of a codegree-four pair has exactly
six vertices. -/
theorem sevenRegular_codegreeFour_symmetricDifference_card_six
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (hreg : ∀ v, D.degree v = 7)
    {x y : V}
    (hcommon : (D.neighborFinset x ∩ D.neighborFinset y).card = 4) :
    ((D.neighborFinset x \ D.neighborFinset y) ∪
      (D.neighborFinset y \ D.neighborFinset x)).card = 6 := by
  obtain ⟨P, Q, hP, hQ, rfl, rfl, hdisj, _⟩ :=
    sevenRegular_codegreeFour_privateTriple_normalization D hreg hcommon
  rw [Finset.card_union_of_disjoint hdisj, hP, hQ]

end

end Erdos85
