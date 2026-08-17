import Proofs.Erdos85NearTwinLitePrivateOwnerSpecialization

/-! # Three identical rows obstruct a two-factor -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A two-regular simple graph cannot have three distinct vertices with the
same adjacency row.  Any neighbor of one would have all three as neighbors. -/
theorem degreeTwo_false_of_three_distinct_equal_adjMatrix_rows
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hdeg : ∀ v, H.degree v = 2)
    {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (habRows : ∀ z, H.adjMatrix ℤ a z = H.adjMatrix ℤ b z)
    (hacRows : ∀ z, H.adjMatrix ℤ a z = H.adjMatrix ℤ c z) : False := by
  have rowAdj {u v : V}
      (hrows : ∀ z, H.adjMatrix ℤ u z = H.adjMatrix ℤ v z) (z : V) :
      H.Adj u z ↔ H.Adj v z := by
    have h := hrows z
    simp only [SimpleGraph.adjMatrix_apply] at h
    by_cases huz : H.Adj u z <;> by_cases hvz : H.Adj v z <;>
      simp_all
  have haCard : (H.neighborFinset a).card = 2 := by
    rw [H.card_neighborFinset_eq_degree, hdeg a]
  have haNonempty : (H.neighborFinset a).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    rw [hempty] at haCard
    simp at haCard
  obtain ⟨z, hza⟩ := haNonempty
  have haz : H.Adj a z := (H.mem_neighborFinset a z).mp hza
  have hbz : H.Adj b z := (rowAdj habRows z).mp haz
  have hcz : H.Adj c z := (rowAdj hacRows z).mp haz
  have hsubset : {a, b, c} ⊆ H.neighborFinset z := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with hw | hw | hw
    · subst w
      exact (H.mem_neighborFinset z a).mpr haz.symm
    · subst w
      exact (H.mem_neighborFinset z b).mpr hbz.symm
    · subst w
      exact (H.mem_neighborFinset z c).mpr hcz.symm
  have hthree : 3 ≤ (H.neighborFinset z).card := by
    have := Finset.card_le_card hsubset
    simpa [hab, hac, hbc] using this
  rw [H.card_neighborFinset_eq_degree, hdeg z] at hthree
  omega

end

end Erdos85
