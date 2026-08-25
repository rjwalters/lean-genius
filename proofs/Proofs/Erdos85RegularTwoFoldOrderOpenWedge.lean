import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# A regular graph on twice its degree has an open wedge

The elementary lemma here is the graph-theoretic core of the size-two
owner edge-regularity argument.  If every pair of neighbors were adjacent,
closed neighborhoods would be pairwise disjoint cliques of order `q + 1`,
which cannot fit in a graph of order `2q`.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A `q`-regular simple graph on `2q` vertices, for `q ≥ 2`, contains an
open wedge: two neighbors of one vertex which are not adjacent. -/
theorem regular_two_mul_order_exists_open_wedge
    {W : Type*} [Fintype W] [DecidableEq W]
    (S : SimpleGraph W) [DecidableRel S.Adj] {q : ℕ}
    (hq : 2 ≤ q) (hcard : Fintype.card W = q * 2)
    (hreg : ∀ x, S.degree x = q) :
    ∃ u v w, S.Adj u v ∧ S.Adj u w ∧ v ≠ w ∧ ¬ S.Adj v w := by
  classical
  by_contra hopen
  push Not at hopen
  have hnonempty : Nonempty W := by
    rw [← Fintype.card_pos_iff, hcard]
    omega
  let u : W := Classical.choice hnonempty
  have hNuCard : (insert u (S.neighborFinset u)).card = q + 1 := by
    rw [Finset.card_insert_of_notMem]
    · simp [S.card_neighborFinset_eq_degree, hreg]
    · simp
  have hNuProper : insert u (S.neighborFinset u) ≠ Finset.univ := by
    intro heq
    have := congrArg Finset.card heq
    simp only [hNuCard, Finset.card_univ, hcard] at this
    omega
  have hex : ∃ z : W, z ∉ insert u (S.neighborFinset u) := by
    by_contra h
    push Not at h
    apply hNuProper
    ext z
    simp [h z]
  obtain ⟨z, hzout⟩ := hex
  have hcross : ∀ y ∈ insert u (S.neighborFinset u), ¬ S.Adj y z := by
    intro y hy hyz
    rw [Finset.mem_insert] at hy
    rcases hy with rfl | hy
    · exact hzout (Finset.mem_insert_of_mem ((S.mem_neighborFinset u z).mpr hyz))
    · have huy : S.Adj u y := (S.mem_neighborFinset u y).mp hy
      have huz : S.Adj u z := hopen y u z huy.symm hyz (fun h => by
        subst z
        exact hzout (Finset.mem_insert_self u _))
      exact hzout (Finset.mem_insert_of_mem ((S.mem_neighborFinset u z).mpr huz))
  have hdisjoint : Disjoint (insert u (S.neighborFinset u))
      (insert z (S.neighborFinset z)) := by
    rw [Finset.disjoint_left]
    intro y hyu hyz
    rw [Finset.mem_insert] at hyz
    rcases hyz with hyz | hyz
    · subst y
      exact hzout hyu
    · exact (hcross y hyu) ((S.mem_neighborFinset z y).mp hyz).symm
  have hNzCard : (insert z (S.neighborFinset z)).card = q + 1 := by
    rw [Finset.card_insert_of_notMem]
    · simp [S.card_neighborFinset_eq_degree, hreg]
    · simp
  have hle := Finset.card_le_card (Finset.subset_univ
    ((insert u (S.neighborFinset u)) ∪ (insert z (S.neighborFinset z))))
  rw [Finset.card_union_of_disjoint hdisjoint, hNuCard, hNzCard] at hle
  simp only [Finset.card_univ] at hle
  rw [hcard] at hle
  omega

#print axioms regular_two_mul_order_exists_open_wedge

end

end Erdos85
