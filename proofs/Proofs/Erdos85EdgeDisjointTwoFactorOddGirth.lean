import Mathlib

/-!
# Edge-disjoint simultaneous two-factor curls have length at least five

The surviving Baer `00` holonomy is seen on one odd port set in two
projections: a secondary owner cycle and a horizontal root-line cycle.
C4-freeness makes their adjacency relations edge-disjoint.  On three
vertices, however, every simple 2-regular graph is the unique triangle, so
two such projections cannot be edge-disjoint.

This is the abstract cross-factor consumer `(73rnz_cjibkzzx)--
(73rnz_cjibkzzy)`.
-/

open SimpleGraph

namespace Erdos85

private theorem neighborFinset_subset_erase_univ
    {P : Type*} [Fintype P] [DecidableEq P]
    (G : SimpleGraph P) [DecidableRel G.Adj] (v : P) :
    G.neighborFinset v ⊆ Finset.univ.erase v := by
  intro u hu
  rw [G.mem_neighborFinset] at hu
  rw [Finset.mem_erase]
  exact ⟨hu.ne', Finset.mem_univ u⟩

private theorem neighborFinset_eq_erase_univ_of_card_three_twoRegular
    {P : Type*} [Fintype P] [DecidableEq P]
    (G : SimpleGraph P) [DecidableRel G.Adj]
    (hcard : Fintype.card P = 3) (hregular : ∀ v, G.degree v = 2) (v : P) :
    G.neighborFinset v = Finset.univ.erase v := by
  apply Finset.eq_of_subset_of_card_le (neighborFinset_subset_erase_univ G v)
  rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ,
    G.card_neighborFinset_eq_degree, hregular v, hcard]

/-- On a three-element vertex type, every simple 2-regular graph contains
every possible edge. -/
theorem adj_of_card_three_twoRegular
    {P : Type*} [Fintype P] [DecidableEq P]
    (G : SimpleGraph P) [DecidableRel G.Adj]
    (hcard : Fintype.card P = 3) (hregular : ∀ v, G.degree v = 2)
    {u v : P} (huv : u ≠ v) : G.Adj u v := by
  have heq := neighborFinset_eq_erase_univ_of_card_three_twoRegular
    G hcard hregular u
  rw [← G.mem_neighborFinset, heq, Finset.mem_erase]
  exact ⟨huv.symm, Finset.mem_univ v⟩

/-- **Simultaneous odd two-factor girth bound (`73rnz_cjibkzzy`).**
Two simple 2-regular factor projections on the same nonempty odd port set,
with no shared adjacency, require at least five ports. -/
theorem five_le_card_of_edgeDisjoint_twoRegular_odd
    {P : Type*} [Fintype P] [DecidableEq P] [Nonempty P]
    (G H : SimpleGraph P) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hG : ∀ v, G.degree v = 2) (hH : ∀ v, H.degree v = 2)
    (hdisjoint : ∀ ⦃u v⦄, G.Adj u v → ¬ H.Adj u v)
    (hodd : Odd (Fintype.card P)) : 5 ≤ Fintype.card P := by
  let v : P := Classical.choice ‹Nonempty P›
  have hsub := neighborFinset_subset_erase_univ G v
  have hthree : 3 ≤ Fintype.card P := by
    have hcardLe := Finset.card_le_card hsub
    rw [G.card_neighborFinset_eq_degree, hG v,
      Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ] at hcardLe
    omega
  have hnotThree : Fintype.card P ≠ 3 := by
    intro hcard
    have hneighCard : (G.neighborFinset v).card = 2 := by
      rw [G.card_neighborFinset_eq_degree, hG v]
    have hneighNonempty : (G.neighborFinset v).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      rw [hempty, Finset.card_empty] at hneighCard
      omega
    obtain ⟨u, hu⟩ := hneighNonempty
    have hGuv : G.Adj v u := by simpa using hu
    have hHuv : H.Adj v u :=
      adj_of_card_three_twoRegular H hcard hH hGuv.ne
    exact hdisjoint hGuv hHuv
  obtain ⟨k, hk⟩ := hodd
  omega

end Erdos85

#print axioms Erdos85.adj_of_card_three_twoRegular
#print axioms Erdos85.five_le_card_of_edgeDisjoint_twoRegular_odd
