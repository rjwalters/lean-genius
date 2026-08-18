import Mathlib

/-! # Normal form for near-twin rows in a seven-regular graph -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- If two vertices of a seven-regular graph have six common neighbors, each
has exactly one neighbor that the other does not.  Away from those two private
neighbors their adjacency rows agree. -/
theorem sevenRegular_nearTwin_privateNeighbor_normalization
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (hreg : ∀ v, D.degree v = 7)
    {x y : V}
    (hcommon : (D.neighborFinset x ∩ D.neighborFinset y).card = 6) :
    ∃ p q : V,
      D.neighborFinset x \ D.neighborFinset y = {p} ∧
      D.neighborFinset y \ D.neighborFinset x = {q} ∧
      p ≠ q ∧
      ∀ z : V, z ≠ p → z ≠ q → (D.Adj x z ↔ D.Adj y z) := by
  have hxcard : (D.neighborFinset x).card = 7 := by
    rw [D.card_neighborFinset_eq_degree, hreg x]
  have hycard : (D.neighborFinset y).card = 7 := by
    rw [D.card_neighborFinset_eq_degree, hreg y]
  have hcommon' : (D.neighborFinset y ∩ D.neighborFinset x).card = 6 := by
    simpa [Finset.inter_comm] using hcommon
  have hxprivate : (D.neighborFinset x \ D.neighborFinset y).card = 1 := by
    rw [Finset.card_sdiff, hcommon', hxcard]
  have hyprivate : (D.neighborFinset y \ D.neighborFinset x).card = 1 := by
    rw [Finset.card_sdiff, hcommon, hycard]
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hxprivate
  obtain ⟨q, hq⟩ := Finset.card_eq_one.mp hyprivate
  refine ⟨p, q, hp, hq, ?_, ?_⟩
  · intro hpq
    subst q
    have hpLeft : p ∈ D.neighborFinset x \ D.neighborFinset y := by simp [hp]
    have hpRight : p ∈ D.neighborFinset y \ D.neighborFinset x := by simp [hq]
    exact (Finset.mem_sdiff.mp hpLeft).2 (Finset.mem_sdiff.mp hpRight).1
  · intro z hzp hzq
    rw [← D.mem_neighborFinset, ← D.mem_neighborFinset]
    constructor
    · intro hxz
      by_contra hyz
      have : z ∈ D.neighborFinset x \ D.neighborFinset y := by simp [hxz, hyz]
      rw [hp] at this
      exact hzp (Finset.mem_singleton.mp this)
    · intro hyz
      by_contra hxz
      have : z ∈ D.neighborFinset y \ D.neighborFinset x := by simp [hyz, hxz]
      rw [hq] at this
      exact hzq (Finset.mem_singleton.mp this)

/-- Set-theoretic row-difference form of near-twin normalization: the
symmetric difference of the two neighbor rows is precisely their two private
neighbors. -/
theorem sevenRegular_nearTwin_neighbor_sdiff_union_eq_pair
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (hreg : ∀ v, D.degree v = 7)
    {x y : V}
    (hcommon : (D.neighborFinset x ∩ D.neighborFinset y).card = 6) :
    ∃ p q : V,
      p ≠ q ∧
      (D.neighborFinset x \ D.neighborFinset y) ∪
          (D.neighborFinset y \ D.neighborFinset x) = {p, q} := by
  obtain ⟨p, q, hp, hq, hpq, _⟩ :=
    sevenRegular_nearTwin_privateNeighbor_normalization D hreg hcommon
  exact ⟨p, q, hpq, by simp [hp, hq]⟩

end

end Erdos85
