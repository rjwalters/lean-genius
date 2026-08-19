import Proofs.Erdos85SizeTwoMuNegThreeSixTenCrossColumnCap

/-! # Multiplicity classification of long signed columns at `mu=-3` -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- A finite function taking only the values zero, one, and two is completely
counted by its three fibers. -/
theorem zero_one_two_fiber_ledger
    {X : Type*} [DecidableEq X] (S : Finset X) (f : X → ℕ)
    (hf : ∀ x ∈ S, f x ≤ 2) :
    let n₀ := (S.filter fun x ↦ f x = 0).card
    let n₁ := (S.filter fun x ↦ f x = 1).card
    let n₂ := (S.filter fun x ↦ f x = 2).card
    n₀ + n₁ + n₂ = S.card ∧
      (∑ x ∈ S, f x) = n₁ + 2 * n₂ := by
  classical
  dsimp only
  induction S using Finset.induction_on with
  | empty => simp
  | @insert x S hx ih =>
      have hfx := hf x (by simp)
      have hfS : ∀ y ∈ S, f y ≤ 2 := by
        intro y hy
        exact hf y (by simp [hy])
      rcases ih hfS with ⟨hicard, hisum⟩
      have hcases : f x = 0 ∨ f x = 1 ∨ f x = 2 := by omega
      rcases hcases with hfx | hfx | hfx <;>
        simp only [Finset.filter_insert, Finset.sum_insert hx] <;>
        simp [hx, hfx, hisum] <;> omega

/-- Two distinct internal components of sizes six and ten exhaust the
sixteen-point defect component. -/
theorem sixTen_internalComponent_complement
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (hc : c.supp.ncard = 16)
    (a b : (G.induce c.supp).ConnectedComponent)
    (ha : a.supp.ncard = 6) (hb : b.supp.ncard = 10) :
    ∀ x : c.supp, x ∉ a.supp ↔ x ∈ b.supp := by
  classical
  let A := (Finset.univ : Finset c.supp).filter fun x ↦ x ∈ a.supp
  let B := (Finset.univ : Finset c.supp).filter fun x ↦ x ∈ b.supp
  have hab : a ≠ b := by
    intro hab
    rw [hab] at ha
    omega
  have hAcard : A.card = 6 := by
    have heq : A = a.supp.toFinite.toFinset := by
      ext x
      simp [A]
    rw [heq, ← Set.ncard_eq_toFinset_card, ha]
  have hBcard : B.card = 10 := by
    have heq : B = b.supp.toFinite.toFinset := by
      ext x
      simp [B]
    rw [heq, ← Set.ncard_eq_toFinset_card, hb]
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hxa hxb
    have hxa' : x ∈ a.supp := (Finset.mem_filter.mp hxa).2
    have hxb' : x ∈ b.supp := (Finset.mem_filter.mp hxb).2
    exact hab <| (ConnectedComponent.mem_supp_iff a x).mp hxa' |>.symm.trans
      ((ConnectedComponent.mem_supp_iff b x).mp hxb')
  have hUcard : (Finset.univ : Finset c.supp).card = 16 := by
    rw [Finset.card_univ]
    calc
      Fintype.card c.supp = c.supp.ncard := by
        simpa [Nat.card_eq_fintype_card] using Nat.card_coe_set_eq c.supp
      _ = 16 := hc
  have hcover : A ∪ B = (Finset.univ : Finset c.supp) := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_union_of_disjoint hdisj, hAcard, hBcard, hUcard]
  intro x
  have hxcover : x ∈ A ∪ B := by rw [hcover]; simp
  simp only [A, B, Finset.mem_union, Finset.mem_filter,
    Finset.mem_univ, true_and] at hxcover
  constructor
  · intro hxa
    exact hxcover.resolve_left hxa
  · intro hxb hxa
    exact hab <| (ConnectedComponent.mem_supp_iff a x).mp hxa |>.symm.trans
      ((ConnectedComponent.mem_supp_iff b x).mp hxb)

set_option maxHeartbeats 800000 in
/-- If `n_i` counts the long columns with exactly `i` same-sign short
neighbors, then `n₀+n₁+n₂=10`, `n₁+2n₂=12`, and hence
`n₂=n₀+2`. In particular only five multiplicity triples remain. -/
theorem orderSixtyFour_sizeTwo_muNegThree_sixTen_crossColumn_types
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (hc : c.supp.ncard = 8 * 2)
    (s : V → ℤ)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c),
        s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z,
        s y = (-3 : ℤ) * s z)
    (a b : (G.induce c.supp).ConnectedComponent)
    (ha : a.supp.ncard = 6) (hb : b.supp.ncard = 10) :
    let K := (secondOrderDefectGraph G).induce c.supp
    let A := (Finset.univ : Finset c.supp).filter fun x ↦ x ∈ a.supp
    let L := (Finset.univ : Finset c.supp).filter fun y ↦ y ∉ a.supp
    let f := fun y ↦ (A.filter fun x ↦
      K.Adj y x ∧ s y.1 = s x.1).card
    let n₀ := (L.filter fun y ↦ f y = 0).card
    let n₁ := (L.filter fun y ↦ f y = 1).card
    let n₂ := (L.filter fun y ↦ f y = 2).card
    n₀ + n₁ + n₂ = 10 ∧ n₁ + 2 * n₂ = 12 ∧
      n₂ = n₀ + 2 ∧ n₀ ≤ 4 := by
  classical
  dsimp only
  let K := (secondOrderDefectGraph G).induce c.supp
  let H := G.induce c.supp
  let A := (Finset.univ : Finset c.supp).filter fun x ↦ x ∈ a.supp
  let L := (Finset.univ : Finset c.supp).filter fun y ↦ y ∉ a.supp
  let f := fun y : c.supp ↦ (A.filter fun x ↦
    K.Adj y x ∧ s y.1 = s x.1).card
  let n₀ := (L.filter fun y ↦ f y = 0).card
  let n₁ := (L.filter fun y ↦ f y = 1).card
  let n₂ := (L.filter fun y ↦ f y = 2).card
  have hcomp := sixTen_internalComponent_complement G c
    (by simpa using hc) a b ha hb
  have hcap := orderSixtyFour_sizeTwo_muNegThree_sixTen_crossColumn_cap
    G hfree hreg hcard c hc s hs_out hs_in hH hD a b ha hb
  have hfle : ∀ y ∈ L, f y ≤ 2 := by
    intro y hy
    have hyb : y ∈ b.supp := (hcomp y).mp (Finset.mem_filter.mp hy).2
    have hc := (hcap y hyb).2.1
    have heq : (A.filter fun x ↦ K.Adj y x ∧ s y.1 = s x.1) =
        ((componentNeighborFinset K H a y).filter fun x ↦
          s x.1 = s y.1) := by
      ext x
      simp only [A, componentNeighborFinset, Finset.mem_filter,
        Finset.mem_univ, true_and, SimpleGraph.mem_neighborFinset]
      aesop
    change (A.filter fun x ↦ K.Adj y x ∧ s y.1 = s x.1).card ≤ 2
    rw [heq]
    exact hc
  have hLcard : L.card = 10 := by
    have hAcard : A.card = 6 := by
      have heq : A = a.supp.toFinite.toFinset := by ext x; simp [A]
      rw [heq, ← Set.ncard_eq_toFinset_card, ha]
    have hcover : A ∪ L = (Finset.univ : Finset c.supp) := by
      ext x
      simp only [A, L, Finset.mem_union, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · intro
        trivial
      · intro
        exact Classical.em (x ∈ a.supp)
    have hdisj : Disjoint A L := by
      rw [Finset.disjoint_left]
      intro x hxa hxl
      exact (Finset.mem_filter.mp hxl).2 (Finset.mem_filter.mp hxa).2
    have hUcard : (Finset.univ : Finset c.supp).card = 16 := by
      rw [Finset.card_univ]
      calc
        Fintype.card c.supp = c.supp.ncard := by
          simpa [Nat.card_eq_fintype_card] using Nat.card_coe_set_eq c.supp
        _ = 16 := by omega
    have := congrArg Finset.card hcover
    rw [Finset.card_union_of_disjoint hdisj, hAcard, hUcard] at this
    omega
  have hledger := zero_one_two_fiber_ledger L f hfle
  have hsum : (∑ y ∈ L, f y) = 12 := by
    have hcensus := orderSixtyFour_sizeTwo_muNegThree_sixTen_crossColumn_census
      G hfree hreg hcard c hc s hs_out hs_in hH hD a b ha hb
    rw [← hcensus.1]
    simp only [Finset.card_sigma]
    rfl
  change n₀ + n₁ + n₂ = L.card ∧
    (∑ y ∈ L, f y) = n₁ + 2 * n₂ at hledger
  change n₀ + n₁ + n₂ = 10 ∧ n₁ + 2 * n₂ = 12 ∧
    n₂ = n₀ + 2 ∧ n₀ ≤ 4
  have hcount := hledger.1
  have hweight := hledger.2
  rw [hLcard] at hcount
  rw [hsum] at hweight
  omega

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegThree_sixTen_crossColumn_types
