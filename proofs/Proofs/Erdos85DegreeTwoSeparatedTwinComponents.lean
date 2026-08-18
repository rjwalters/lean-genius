import Proofs.Erdos85DegreeTwoRepeatedForkSaturation

/-! # Separated twin pairs occupy distinct four-cycles -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A distinct equal-neighborhood pair in a two-regular graph occupies an
entire connected component of order four.  No global hypothesis on the other
component sizes is needed. -/
theorem degreeTwo_equalNeighbors_component_order_four_unconditional
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) [DecidableRel F.Adj]
    (hdeg : ∀ v, F.degree v = 2)
    {a b : V} (hab : a ≠ b)
    (hN : F.neighborFinset a = F.neighborFinset b) :
    (F.connectedComponentMk a).supp.ncard = 4 := by
  classical
  have hcardN : (F.neighborFinset a).card = 2 := by
    rw [F.card_neighborFinset_eq_degree, hdeg a]
  obtain ⟨r, s, hrs, hNas⟩ := Finset.card_eq_two.mp hcardN
  have har : F.Adj a r := by
    rw [← F.mem_neighborFinset, hNas]
    simp
  have has : F.Adj a s := by
    rw [← F.mem_neighborFinset, hNas]
    simp
  have hbr : F.Adj b r := by
    rw [← F.mem_neighborFinset, ← hN, hNas]
    simp
  have hbs : F.Adj b s := by
    rw [← F.mem_neighborFinset, ← hN, hNas]
    simp
  let S : Finset V := {a, b, r, s}
  obtain ⟨hScard, hclosed⟩ := degreeTwo_repeatedFork_closed_card_four
    F hdeg hab hrs har hbr has hbs
  let K := F.connectedComponentMk a
  have reachable_mem_S : ∀ v, F.Reachable a v → v ∈ S := by
    intro v hreach
    rw [reachable_eq_reflTransGen] at hreach
    have haS : a ∈ S := by simp [S]
    induction hreach with
    | refl => exact haS
    | tail hpath hadj ih =>
        exact hclosed _ ih ((F.mem_neighborFinset _ _).mpr hadj)
  have hSupp : K.supp = (S : Set V) := by
    ext v
    constructor
    · intro hv
      have hreach : F.Reachable a v :=
        ConnectedComponent.reachable_of_mem_supp K
          ConnectedComponent.connectedComponentMk_mem hv
      exact reachable_mem_S v hreach
    · intro hv
      change v ∈ ({a, b, r, s} : Finset V) at hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl | rfl
      · exact ConnectedComponent.connectedComponentMk_mem
      · exact (K.mem_supp_congr_adj hbr).mpr
          ((K.mem_supp_congr_adj har).mp
            ConnectedComponent.connectedComponentMk_mem)
      · exact (K.mem_supp_congr_adj har).mp
          ConnectedComponent.connectedComponentMk_mem
      · exact (K.mem_supp_congr_adj has).mp
          ConnectedComponent.connectedComponentMk_mem
  rw [hSupp, Set.ncard_coe_finset, hScard]

/-- Two vertex-disjoint equal-neighborhood pairs with one missing cross edge
occupy two distinct order-four connected components of a two-factor. -/
theorem degreeTwo_two_separated_equalPairs_distinct_fourComponents
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) [DecidableRel F.Adj]
    (hdeg : ∀ v, F.degree v = 2)
    {a b p q : V}
    (hab : a ≠ b) (hpq : p ≠ q)
    (hap : a ≠ p) (haq : a ≠ q) (hbp : b ≠ p) (hbq : b ≠ q)
    (hNab : F.neighborFinset a = F.neighborFinset b)
    (hNpq : F.neighborFinset p = F.neighborFinset q)
    (hcross : ¬F.Adj a p) :
    let A := F.connectedComponentMk a
    let P := F.connectedComponentMk p
    A.supp.ncard = 4 ∧ P.supp.ncard = 4 ∧ A ≠ P := by
  classical
  let A := F.connectedComponentMk a
  let P := F.connectedComponentMk p
  have hA4 : A.supp.ncard = 4 :=
    degreeTwo_equalNeighbors_component_order_four_unconditional
      F hdeg hab hNab
  have hP4 : P.supp.ncard = 4 :=
    degreeTwo_equalNeighbors_component_order_four_unconditional
      F hdeg hpq hNpq
  refine ⟨hA4, hP4, ?_⟩
  intro hAP
  have hpSupp : p ∈ A.supp := by
    exact (ConnectedComponent.mem_supp_iff A p).mpr hAP.symm
  have hcardN : (F.neighborFinset a).card = 2 := by
    rw [F.card_neighborFinset_eq_degree, hdeg a]
  obtain ⟨r, s, hrs, hNas⟩ := Finset.card_eq_two.mp hcardN
  have har : F.Adj a r := by
    rw [← F.mem_neighborFinset, hNas]
    simp
  have has : F.Adj a s := by
    rw [← F.mem_neighborFinset, hNas]
    simp
  have hbr : F.Adj b r := by
    rw [← F.mem_neighborFinset, ← hNab, hNas]
    simp
  have hbs : F.Adj b s := by
    rw [← F.mem_neighborFinset, ← hNab, hNas]
    simp
  let S : Finset V := {a, b, r, s}
  have hSsub : (S : Set V) ⊆ A.supp := by
    intro v hv
    change v ∈ ({a, b, r, s} : Finset V) at hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact ConnectedComponent.connectedComponentMk_mem
    · exact (A.mem_supp_congr_adj hbr).mpr
        ((A.mem_supp_congr_adj har).mp
          ConnectedComponent.connectedComponentMk_mem)
    · exact (A.mem_supp_congr_adj har).mp
        ConnectedComponent.connectedComponentMk_mem
    · exact (A.mem_supp_congr_adj has).mp
        ConnectedComponent.connectedComponentMk_mem
  have hScard : S.card = 4 :=
    (degreeTwo_repeatedFork_closed_card_four
      F hdeg hab hrs har hbr has hbs).1
  have hSuppEq : A.supp = (S : Set V) := by
    apply (Set.eq_of_subset_of_ncard_le hSsub ?_).symm
    rw [Set.ncard_coe_finset, hScard, hA4]
  rw [hSuppEq] at hpSupp
  change p ∈ ({a, b, r, s} : Finset V) at hpSupp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hpSupp
  rcases hpSupp with hpa | hpb | hpr | hps
  · exact hap hpa.symm
  · exact hbp hpb.symm
  · exact hcross (hpr ▸ har)
  · exact hcross (hps ▸ has)

end

end Erdos85
