import Proofs.Erdos85SizeTwoMuNegThreeCrossOwnerConstraints

/-! # Unified owner/collision normal form at `mu = -3` -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- A single coherent choice of normalized cross matchings and their exterior
ambient owners. The exhaustion field ensures later collision arguments refer
to these exact choices, rather than to a second existential normal form. -/
structure MuNegThreeCrossOwnerNormalForm
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (c : (secondOrderDefectGraph G).ConnectedComponent) (s : V → ℤ) where
  f : MuNegThreePositiveShore (secondOrderDefectGraph G) c s ≃
    MuNegThreeNegativeShore (secondOrderDefectGraph G) c s
  σ : Equiv.Perm (MuNegThreePositiveShore (secondOrderDefectGraph G) c s)
  τ : Equiv.Perm (MuNegThreePositiveShore (secondOrderDefectGraph G) c s)
  o₀ : MuNegThreePositiveShore (secondOrderDefectGraph G) c s → V
  oσ : MuNegThreePositiveShore (secondOrderDefectGraph G) c s → V
  oτ : MuNegThreePositiveShore (secondOrderDefectGraph G) c s → V
  σ_ne : ∀ x, σ x ≠ x
  τ_ne : ∀ x, τ x ≠ x
  στ_ne : ∀ x, σ x ≠ τ x
  exhaust : ∀ x y, ¬ (secondOrderDefectGraph G).Adj x.1 y.1 ↔
    y = f x ∨ y = f (σ x) ∨ y = f (τ x)
  owner₀ : ∀ x z, (G.Adj x.1 z ∧ G.Adj (f x).1 z) ↔ z = o₀ x
  ownerσ : ∀ x z, (G.Adj x.1 z ∧ G.Adj (f (σ x)).1 z) ↔ z = oσ x
  ownerτ : ∀ x z, (G.Adj x.1 z ∧ G.Adj (f (τ x)).1 z) ↔ z = oτ x
  o₀_out : ∀ x, o₀ x ∉ c.supp
  oσ_out : ∀ x, oσ x ∉ c.supp
  oτ_out : ∀ x, oτ x ∉ c.supp

/-- The `mu = -3` hypotheses produce one coherent cross-owner normal form. -/
theorem orderSixtyFour_sizeTwo_muNegThree_exists_crossOwnerNormalForm
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
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c),
        s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z,
        s y = (-3 : ℤ) * s z) :
    Nonempty (MuNegThreeCrossOwnerNormalForm G c s) := by
  classical
  let D := secondOrderDefectGraph G
  let Xp := MuNegThreePositiveShore D c s
  let Xm := MuNegThreeNegativeShore D c s
  obtain ⟨f, σ, τ, o₀, oσ, oτ, hσne, hτne, hστ,
      ho₀, hoσ, hoτ, ho₀out, hoσout, hoτout⟩ :=
    orderSixtyFour_sizeTwo_muNegThree_cross_nondefect_ownerNormalForm
      G hfree hreg hcard c hc s hs_out hs_in hH hD
  have hf (x : Xp) : ¬ D.Adj x.1 (f x).1 := by
    have hx := (ho₀ x (o₀ x)).2 rfl
    exact (orderSixtyFour_sizeTwo_muNegThree_cross_owner_rectangle
      G hfree c s x x (f x) (f x) (o₀ x) hx hx).1
  have hfs (x : Xp) : ¬ D.Adj x.1 (f (σ x)).1 := by
    have hx := (hoσ x (oσ x)).2 rfl
    exact (orderSixtyFour_sizeTwo_muNegThree_cross_owner_rectangle
      G hfree c s x x (f (σ x)) (f (σ x)) (oσ x) hx hx).1
  have hft (x : Xp) : ¬ D.Adj x.1 (f (τ x)).1 := by
    have hx := (hoτ x (oτ x)).2 rfl
    exact (orderSixtyFour_sizeTwo_muNegThree_cross_owner_rectangle
      G hfree c s x x (f (τ x)) (f (τ x)) (oτ x) hx hx).1
  have hcubic := orderSixtyFour_sizeTwo_muNegThree_cross_nondefect_threeRegular
    G hfree hreg hcard c hc s hs_out hs_in hH hD
  have hexhaust : ∀ x : Xp, ∀ y : Xm, ¬ D.Adj x.1 y.1 ↔
      y = f x ∨ y = f (σ x) ∨ y = f (τ x) := by
    intro x y
    let S : Finset Xm := Finset.univ.filter fun v ↦ ¬ D.Adj x.1 v.1
    have hm0 : f x ∈ S := by simpa [S] using hf x
    have hm1 : f (σ x) ∈ S := by simpa [S] using hfs x
    have hm2 : f (τ x) ∈ S := by simpa [S] using hft x
    have h01 : f x ≠ f (σ x) := f.injective.ne (Ne.symm (hσne x))
    have h02 : f x ≠ f (τ x) := f.injective.ne (Ne.symm (hτne x))
    have h12 : f (σ x) ≠ f (τ x) := f.injective.ne (hστ x)
    have hsub : {f x, f (σ x), f (τ x)} ⊆ S := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl
      · exact hm0
      · exact hm1
      · exact hm2
    have hthree : ({f x, f (σ x), f (τ x)} : Finset Xm).card = 3 :=
      Finset.card_eq_three.mpr ⟨f x, f (σ x), f (τ x), h01, h02, h12, rfl⟩
    have hScard : S.card = 3 := hcubic.1 x
    have heq : {f x, f (σ x), f (τ x)} = S :=
      Finset.eq_of_subset_of_card_le hsub (by omega)
    constructor
    · intro hy
      have hyS : y ∈ S := by simpa [S] using hy
      rw [← heq] at hyS
      simpa using hyS
    · intro hy
      have hyS : y ∈ ({f x, f (σ x), f (τ x)} : Finset Xm) := by
        simpa using hy
      rw [heq] at hyS
      simpa [S] using hyS
  exact ⟨{
    f := f, σ := σ, τ := τ, o₀ := o₀, oσ := oσ, oτ := oτ,
    σ_ne := hσne, τ_ne := hτne, στ_ne := hστ, exhaust := hexhaust,
    owner₀ := ho₀, ownerσ := hoσ, ownerτ := hoτ,
    o₀_out := ho₀out, oσ_out := hoσout, oτ_out := hoτout }⟩

/-- Concrete diagonal collision laws for the three owner maps in a coherent
normal form. In particular, every owner fibre is supported on at most the
three normalized positions visible from any one of its sources. -/
theorem MuNegThreeCrossOwnerNormalForm.diagonal_collision_laws
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (c : (secondOrderDefectGraph G).ConnectedComponent) (s : V → ℤ)
    (N : MuNegThreeCrossOwnerNormalForm G c s) :
    (∀ x x', N.o₀ x = N.o₀ x' →
      x' = x ∨ x' = N.σ x ∨ x' = N.τ x) ∧
    (∀ x x', N.oσ x = N.oσ x' →
      N.σ x' = x ∨ N.σ x' = N.σ x ∨ N.σ x' = N.τ x) ∧
    ∀ x x', N.oτ x = N.oτ x' →
      N.τ x' = x ∨ N.τ x' = N.σ x ∨ N.τ x' = N.τ x := by
  constructor
  · intro x x' howner
    exact orderSixtyFour_sizeTwo_muNegThree_cross_owner_collision_index
      G hfree c s N.f N.σ N.τ (fun u ↦ u) (fun u ↦ u) N.o₀ N.o₀
        N.exhaust N.owner₀ N.owner₀ howner
  constructor
  · intro x x' howner
    exact orderSixtyFour_sizeTwo_muNegThree_cross_owner_collision_index
      G hfree c s N.f N.σ N.τ N.σ N.σ N.oσ N.oσ
        N.exhaust N.ownerσ N.ownerσ howner
  · intro x x' howner
    exact orderSixtyFour_sizeTwo_muNegThree_cross_owner_collision_index
      G hfree c s N.f N.σ N.τ N.τ N.τ N.oτ N.oτ
        N.exhaust N.ownerτ N.ownerτ howner

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegThree_exists_crossOwnerNormalForm
#print axioms Erdos85.MuNegThreeCrossOwnerNormalForm.diagonal_collision_laws
