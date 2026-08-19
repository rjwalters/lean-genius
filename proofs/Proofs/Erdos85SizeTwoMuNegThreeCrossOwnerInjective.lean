import Proofs.Erdos85SizeTwoMuNegThreeCrossOwnerCollisionNormalForm
import Proofs.Erdos85BinarySquareMuThreeExteriorGrid

/-! # Distinct exterior cross owners at `mu = -3` -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- An exterior vertex of a normalized size-two component has exactly two
component neighbours. Hence, if it owns two positive/negative cross pairs,
their positive endpoints and their negative endpoints coincide. -/
theorem orderSixtyFour_sizeTwo_cross_exterior_owner_endpoints_unique
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
    (hc : c.supp.ncard = 8 * 2)
    (s : V → ℤ)
    (x x' : MuNegThreePositiveShore (secondOrderDefectGraph G) c s)
    (y y' : MuNegThreeNegativeShore (secondOrderDefectGraph G) c s)
    (z : V)
    (hz : G.Adj x.1 z ∧ G.Adj y.1 z)
    (hz' : G.Adj x'.1 z ∧ G.Adj y'.1 z) :
    x = x' ∧ y = y' := by
  classical
  let D := secondOrderDefectGraph G
  let C := componentNeighborFinset G D c z
  have hmul := binarySquare_regular_mul_componentNeighborCard_eq_componentCard
    G hfree (q := 8) (by norm_num) hreg hcard
      (D.connectedComponentMk z) c (x := z)
      ((ConnectedComponent.mem_supp_iff _ z).mpr rfl)
  rw [hc] at hmul
  have hCcard : C.card = 2 := by
    change (componentNeighborFinset G D c z).card = 2
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 8) hmul
  have hmem (u : V) (huc : u ∈ c.supp) (huz : G.Adj u z) : u ∈ C := by
    apply Finset.mem_filter.mpr
    exact ⟨(G.mem_neighborFinset z u).mpr huz.symm,
      (ConnectedComponent.mem_supp_iff c u).mp huc⟩
  have hxmem : x.1 ∈ C := hmem x.1 x.2.1 hz.1
  have hymem : y.1 ∈ C := hmem y.1 y.2.1 hz.2
  have hx'mem : x'.1 ∈ C := hmem x'.1 x'.2.1 hz'.1
  have hy'mem : y'.1 ∈ C := hmem y'.1 y'.2.1 hz'.2
  have hxy : x.1 ≠ y.1 := by
    intro h
    have hsxy : s x.1 = s y.1 := congrArg s h
    omega
  have hsub : ({x.1, y.1} : Finset V) ⊆ C := by
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact hxmem
    · exact hymem
  have hpCard : ({x.1, y.1} : Finset V).card = 2 := by simp [hxy]
  have heq : ({x.1, y.1} : Finset V) = C :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  have hx'cases : x'.1 = x.1 ∨ x'.1 = y.1 := by
    rw [← heq] at hx'mem
    simpa [eq_comm] using hx'mem
  have hy'cases : y'.1 = x.1 ∨ y'.1 = y.1 := by
    rw [← heq] at hy'mem
    simpa [eq_comm] using hy'mem
  constructor
  · apply Subtype.ext
    rcases hx'cases with h | h
    · exact h.symm
    · have hsbad : s x'.1 = s y.1 := congrArg s h
      omega
  · apply Subtype.ext
    rcases hy'cases with h | h
    · have hsbad : s y'.1 = s x.1 := congrArg s h
      omega
    · exact h.symm

/-- The three coherent cross-owner maps are injective and have pairwise
disjoint images. Thus the 24 normalized cross-nondefect pairs have 24
different exterior owners. -/
theorem MuNegThreeCrossOwnerNormalForm.owner_maps_injective_disjoint
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
    (hc : c.supp.ncard = 8 * 2) (s : V → ℤ)
    (N : MuNegThreeCrossOwnerNormalForm G c s) :
    Function.Injective N.o₀ ∧ Function.Injective N.oσ ∧
    Function.Injective N.oτ ∧
    Disjoint (Finset.univ.image N.o₀) (Finset.univ.image N.oσ) ∧
    Disjoint (Finset.univ.image N.o₀) (Finset.univ.image N.oτ) ∧
    Disjoint (Finset.univ.image N.oσ) (Finset.univ.image N.oτ) := by
  have hinj₀ : Function.Injective N.o₀ := by
    intro x x' howner
    have hx := (N.owner₀ x (N.o₀ x)).2 rfl
    have hx' := (N.owner₀ x' (N.o₀ x')).2 rfl
    rw [← howner] at hx'
    exact (orderSixtyFour_sizeTwo_cross_exterior_owner_endpoints_unique
      G hfree hreg hcard c hc s x x' (N.f x) (N.f x') (N.o₀ x) hx hx').1
  have hinjσ : Function.Injective N.oσ := by
    intro x x' howner
    have hx := (N.ownerσ x (N.oσ x)).2 rfl
    have hx' := (N.ownerσ x' (N.oσ x')).2 rfl
    rw [← howner] at hx'
    exact (orderSixtyFour_sizeTwo_cross_exterior_owner_endpoints_unique
      G hfree hreg hcard c hc s x x' (N.f (N.σ x)) (N.f (N.σ x'))
        (N.oσ x) hx hx').1
  have hinjτ : Function.Injective N.oτ := by
    intro x x' howner
    have hx := (N.ownerτ x (N.oτ x)).2 rfl
    have hx' := (N.ownerτ x' (N.oτ x')).2 rfl
    rw [← howner] at hx'
    exact (orderSixtyFour_sizeTwo_cross_exterior_owner_endpoints_unique
      G hfree hreg hcard c hc s x x' (N.f (N.τ x)) (N.f (N.τ x'))
        (N.oτ x) hx hx').1
  have hd0σ : Disjoint (Finset.univ.image N.o₀) (Finset.univ.image N.oσ) := by
    rw [Finset.disjoint_left]
    intro z hz0 hzσ
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hz0
    obtain ⟨x', -, howner⟩ := Finset.mem_image.mp hzσ
    have hx := (N.owner₀ x (N.o₀ x)).2 rfl
    have hx' := (N.ownerσ x' (N.oσ x')).2 rfl
    rw [howner] at hx'
    have H := orderSixtyFour_sizeTwo_cross_exterior_owner_endpoints_unique
      G hfree hreg hcard c hc s x x' (N.f x) (N.f (N.σ x'))
        (N.o₀ x) hx hx'
    have hidx : x = N.σ x' := N.f.injective H.2
    rw [H.1] at hidx
    exact N.σ_ne x' hidx.symm
  have hd0τ : Disjoint (Finset.univ.image N.o₀) (Finset.univ.image N.oτ) := by
    rw [Finset.disjoint_left]
    intro z hz0 hzτ
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hz0
    obtain ⟨x', -, howner⟩ := Finset.mem_image.mp hzτ
    have hx := (N.owner₀ x (N.o₀ x)).2 rfl
    have hx' := (N.ownerτ x' (N.oτ x')).2 rfl
    rw [howner] at hx'
    have H := orderSixtyFour_sizeTwo_cross_exterior_owner_endpoints_unique
      G hfree hreg hcard c hc s x x' (N.f x) (N.f (N.τ x'))
        (N.o₀ x) hx hx'
    have hidx : x = N.τ x' := N.f.injective H.2
    rw [H.1] at hidx
    exact N.τ_ne x' hidx.symm
  have hdστ : Disjoint (Finset.univ.image N.oσ) (Finset.univ.image N.oτ) := by
    rw [Finset.disjoint_left]
    intro z hzσ hzτ
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hzσ
    obtain ⟨x', -, howner⟩ := Finset.mem_image.mp hzτ
    have hx := (N.ownerσ x (N.oσ x)).2 rfl
    have hx' := (N.ownerτ x' (N.oτ x')).2 rfl
    rw [howner] at hx'
    have H := orderSixtyFour_sizeTwo_cross_exterior_owner_endpoints_unique
      G hfree hreg hcard c hc s x x' (N.f (N.σ x)) (N.f (N.τ x'))
        (N.oσ x) hx hx'
    have hidx : N.σ x = N.τ x' := N.f.injective H.2
    rw [H.1] at hidx
    exact N.στ_ne x' hidx
  exact ⟨hinj₀, hinjσ, hinjτ, hd0σ, hd0τ, hdστ⟩

/-- The three matching owner maps occupy exactly 24 distinct exterior
vertices: eight for each matching and no overlap between matchings. -/
theorem MuNegThreeCrossOwnerNormalForm.cross_owner_union_card_twentyFour
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
    (hc : c.supp.ncard = 8 * 2) (s : V → ℤ)
    (N : MuNegThreeCrossOwnerNormalForm G c s)
    (hshore : Fintype.card
      (MuNegThreePositiveShore (secondOrderDefectGraph G) c s) = 8) :
    ((Finset.univ.image N.o₀ ∪ Finset.univ.image N.oσ) ∪
      Finset.univ.image N.oτ).card = 24 := by
  let A := Finset.univ.image N.o₀
  let B := Finset.univ.image N.oσ
  let C := Finset.univ.image N.oτ
  obtain ⟨hi0, hiσ, hiτ, hd0σ, hd0τ, hdστ⟩ :=
    N.owner_maps_injective_disjoint G hfree hreg hcard c hc s
  have hA : A.card = 8 := by
    dsimp [A]
    rw [Finset.card_image_of_injective _ hi0, Finset.card_univ, hshore]
  have hB : B.card = 8 := by
    dsimp [B]
    rw [Finset.card_image_of_injective _ hiσ, Finset.card_univ, hshore]
  have hC : C.card = 8 := by
    dsimp [C]
    rw [Finset.card_image_of_injective _ hiτ, Finset.card_univ, hshore]
  have hdAB : Disjoint A B := by simpa [A, B] using hd0σ
  have hdAC : Disjoint A C := by simpa [A, C] using hd0τ
  have hdBC : Disjoint B C := by simpa [B, C] using hdστ
  have hdABC : Disjoint (A ∪ B) C := Finset.disjoint_union_left.mpr ⟨hdAC, hdBC⟩
  change ((A ∪ B) ∪ C).card = 24
  rw [Finset.card_union_of_disjoint hdABC,
    Finset.card_union_of_disjoint hdAB, hA, hB, hC]

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_cross_exterior_owner_endpoints_unique
#print axioms Erdos85.MuNegThreeCrossOwnerNormalForm.owner_maps_injective_disjoint
#print axioms Erdos85.MuNegThreeCrossOwnerNormalForm.cross_owner_union_card_twentyFour
