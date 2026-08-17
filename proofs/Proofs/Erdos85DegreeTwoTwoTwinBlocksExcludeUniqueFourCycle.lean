import Proofs.Erdos85OrderSixtyFourFiveCrossComponentsOwnerProfile

/-! # Two separated twin pairs exclude a unique four-cycle profile -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- In a two-regular graph whose components all have order three or four, a
distinct equal-neighborhood pair belongs to an order-four component. -/
theorem degreeTwo_equalNeighbors_component_order_four
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) [DecidableRel F.Adj]
    (hdeg : ∀ v, F.degree v = 2)
    (hshape : ∀ K : F.ConnectedComponent,
      K.supp.ncard = 3 ∨ K.supp.ncard = 4)
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
  let K := F.connectedComponentMk a
  let S := K.supp.toFinite.toFinset
  have haSupp : a ∈ K.supp := by
    rw [ConnectedComponent.mem_supp_iff]
  have hrSupp : r ∈ K.supp := by
    rw [ConnectedComponent.mem_supp_iff]
    exact (ConnectedComponent.connectedComponentMk_eq_of_adj har).symm
  have hsSupp : s ∈ K.supp := by
    rw [ConnectedComponent.mem_supp_iff]
    exact (ConnectedComponent.connectedComponentMk_eq_of_adj has).symm
  have hbSupp : b ∈ K.supp := by
    rw [ConnectedComponent.mem_supp_iff]
    exact calc
      F.connectedComponentMk b = F.connectedComponentMk r :=
        ConnectedComponent.connectedComponentMk_eq_of_adj hbr
      _ = F.connectedComponentMk a :=
        (ConnectedComponent.connectedComponentMk_eq_of_adj har).symm
  have haS : a ∈ S := by simpa [S] using haSupp
  have hbS : b ∈ S := by simpa [S] using hbSupp
  have hrS : r ∈ S := by simpa [S] using hrSupp
  have hsS : s ∈ S := by simpa [S] using hsSupp
  have hsub : ({a, b, r, s} : Finset V) ⊆ S := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨haS, hbS, hrS, hsS⟩
  have harne : a ≠ r := F.ne_of_adj har
  have hasne : a ≠ s := F.ne_of_adj has
  have hbrne : b ≠ r := F.ne_of_adj hbr
  have hbsne : b ≠ s := F.ne_of_adj hbs
  have hfour : ({a, b, r, s} : Finset V).card = 4 := by
    simp [hab, hrs, harne, hasne, hbrne, hbsne]
  have hKge : 4 ≤ K.supp.ncard := by
    have hle := Finset.card_le_card hsub
    rw [hfour] at hle
    have hScard : S.card = K.supp.ncard := by
      simpa [S] using
        (Set.ncard_eq_toFinset_card K.supp K.supp.toFinite).symm
    omega
  rcases hshape K with h3 | h4
  · omega
  · exact h4

/-- Two disjoint equal-neighborhood pairs cannot coexist when the graph has a
unique order-four component and every component has order three or four. -/
theorem degreeTwo_false_of_two_separated_equalNeighbor_pairs_unique_four
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) [DecidableRel F.Adj]
    (hdeg : ∀ v, F.degree v = 2)
    (hunique : ∃! K : F.ConnectedComponent, K.supp.ncard = 4)
    (hshape : ∀ K : F.ConnectedComponent,
      K.supp.ncard = 3 ∨ K.supp.ncard = 4)
    {a b p q : V}
    (hab : a ≠ b) (hpq : p ≠ q)
    (hap : a ≠ p) (hbp : b ≠ p)
    (hNab : F.neighborFinset a = F.neighborFinset b)
    (hNpq : F.neighborFinset p = F.neighborFinset q)
    (hcross : ¬F.Adj a p) : False := by
  classical
  let A := F.connectedComponentMk a
  let P := F.connectedComponentMk p
  have hA4 : A.supp.ncard = 4 :=
    degreeTwo_equalNeighbors_component_order_four F hdeg hshape hab hNab
  have hP4 : P.supp.ncard = 4 :=
    degreeTwo_equalNeighbors_component_order_four F hdeg hshape hpq hNpq
  obtain ⟨K, hK4, hKunique⟩ := hunique
  have hAK : A = K := hKunique A hA4
  have hPK : P = K := hKunique P hP4
  have hAP : A = P := hAK.trans hPK.symm
  have hpSupp : p ∈ A.supp := by
    rw [hAP, ConnectedComponent.mem_supp_iff]
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
  let S := A.supp.toFinite.toFinset
  have haSupp : a ∈ A.supp := by
    rw [ConnectedComponent.mem_supp_iff]
  have hbSupp : b ∈ A.supp := by
    rw [ConnectedComponent.mem_supp_iff]
    exact calc
      F.connectedComponentMk b = F.connectedComponentMk r :=
        ConnectedComponent.connectedComponentMk_eq_of_adj hbr
      _ = F.connectedComponentMk a :=
        (ConnectedComponent.connectedComponentMk_eq_of_adj har).symm
  have hrSupp : r ∈ A.supp := by
    rw [ConnectedComponent.mem_supp_iff]
    exact (ConnectedComponent.connectedComponentMk_eq_of_adj har).symm
  have hsSupp : s ∈ A.supp := by
    rw [ConnectedComponent.mem_supp_iff]
    exact (ConnectedComponent.connectedComponentMk_eq_of_adj has).symm
  have haS : a ∈ S := by simpa [S] using haSupp
  have hbS : b ∈ S := by simpa [S] using hbSupp
  have hrS : r ∈ S := by simpa [S] using hrSupp
  have hsS : s ∈ S := by simpa [S] using hsSupp
  have hsub : ({a, b, r, s} : Finset V) ⊆ S := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨haS, hbS, hrS, hsS⟩
  have hfour : ({a, b, r, s} : Finset V).card = 4 := by
    have harne : a ≠ r := F.ne_of_adj har
    have hasne : a ≠ s := F.ne_of_adj has
    have hbrne : b ≠ r := F.ne_of_adj hbr
    have hbsne : b ≠ s := F.ne_of_adj hbs
    simp [hab, hrs, harne, hasne, hbrne, hbsne]
  have hScard : S.card = 4 := by
    simpa [S] using
      (Set.ncard_eq_toFinset_card A.supp A.supp.toFinite).symm.trans hA4
  have hSeq : ({a, b, r, s} : Finset V) = S :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hfour, hScard])
  have hpS : p ∈ S := by simpa [S] using hpSupp
  rw [← hSeq] at hpS
  simp only [Finset.mem_insert, Finset.mem_singleton] at hpS
  rcases hpS with hpa | hpb | hpr | hps
  · exact hap hpa.symm
  · exact hbp hpb.symm
  · exact hcross (hpr ▸ har)
  · exact hcross (hps ▸ has)

end

end Erdos85
