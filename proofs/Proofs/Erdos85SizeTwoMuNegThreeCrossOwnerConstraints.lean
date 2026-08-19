import Proofs.Erdos85SizeTwoMuNegThreeCrossOwners

/-! # Collision constraints for `mu = -3` cross-pair owners -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- If two cross-shore pairs have the same ambient owner, then the two
crossed pairs are nondefect as well. Thus every owner fibre cuts out a
complete bipartite rectangle in the cubic cross-nondefect relation. -/
theorem orderSixtyFour_sizeTwo_muNegThree_cross_owner_rectangle
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (s : V → ℤ)
    (x x' : MuNegThreePositiveShore (secondOrderDefectGraph G) c s)
    (y y' : MuNegThreeNegativeShore (secondOrderDefectGraph G) c s)
    (z : V)
    (hz : G.Adj x.1 z ∧ G.Adj y.1 z)
    (hz' : G.Adj x'.1 z ∧ G.Adj y'.1 z) :
    ¬ (secondOrderDefectGraph G).Adj x.1 y'.1 ∧
      ¬ (secondOrderDefectGraph G).Adj x'.1 y.1 := by
  have hne (u : MuNegThreePositiveShore (secondOrderDefectGraph G) c s)
      (v : MuNegThreeNegativeShore (secondOrderDefectGraph G) c s) :
      u.1 ≠ v.1 := by
    intro huv
    have hsuv : s u.1 = s v.1 := congrArg s huv
    omega
  constructor
  · intro hxy'
    have hzero :=
      (secondOrderDefectGraph_adj_iff_card_common_eq_zero
        G hfree (hne x y')).mp hxy'
    have hmem : z ∈ G.neighborFinset x.1 ∩ G.neighborFinset y'.1 := by
      simp [hz.1, hz'.2]
    rw [Finset.card_eq_zero.mp hzero] at hmem
    simp at hmem
  · intro hx'y
    have hzero :=
      (secondOrderDefectGraph_adj_iff_card_common_eq_zero
        G hfree (hne x' y)).mp hx'y
    have hmem : z ∈ G.neighborFinset x'.1 ∩ G.neighborFinset y.1 := by
      simp [hz'.1, hz.2]
    rw [Finset.card_eq_zero.mp hzero] at hmem
    simp at hmem

/-- The three normalized perfect matchings are not merely disjoint: they
exhaust the cubic cross-nondefect relation pointwise. -/
theorem orderSixtyFour_sizeTwo_muNegThree_cross_nondefect_permutationExhaustion
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
    let D := secondOrderDefectGraph G
    let Xp := MuNegThreePositiveShore D c s
    let Xm := MuNegThreeNegativeShore D c s
    ∃ f : Xp ≃ Xm, ∃ σ τ : Equiv.Perm Xp,
      (∀ x, σ x ≠ x) ∧ (∀ x, τ x ≠ x) ∧ (∀ x, σ x ≠ τ x) ∧
      ∀ x y, ¬ D.Adj x.1 y.1 ↔
        y = f x ∨ y = f (σ x) ∨ y = f (τ x) := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let Xp := MuNegThreePositiveShore D c s
  let Xm := MuNegThreeNegativeShore D c s
  obtain ⟨f, σ, τ, hf, hσ, hτ, hσne, hτne, hστ⟩ :=
    orderSixtyFour_sizeTwo_muNegThree_cross_nondefect_permutationNormalForm
      G hfree hreg hcard c hc s hs_out hs_in hH hD
  have hcubic := orderSixtyFour_sizeTwo_muNegThree_cross_nondefect_threeRegular
    G hfree hreg hcard c hc s hs_out hs_in hH hD
  refine ⟨f, σ, τ, hσne, hτne, hστ, ?_⟩
  intro x y
  let S : Finset Xm := Finset.univ.filter fun v ↦ ¬ D.Adj x.1 v.1
  have hfx : f x ∈ S := by simpa [S, D] using hf x
  have hfs : f (σ x) ∈ S := by simpa [S, D] using hσ x
  have hft : f (τ x) ∈ S := by simpa [S, D] using hτ x
  have h01 : f x ≠ f (σ x) :=
    f.injective.ne (Ne.symm (hσne x))
  have h02 : f x ≠ f (τ x) :=
    f.injective.ne (Ne.symm (hτne x))
  have h12 : f (σ x) ≠ f (τ x) := f.injective.ne (hστ x)
  have hsmall : {f x, f (σ x), f (τ x)} ⊆ S := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact hfx
    · exact hfs
    · exact hft
  have hthree : ({f x, f (σ x), f (τ x)} : Finset Xm).card = 3 :=
    Finset.card_eq_three.mpr ⟨f x, f (σ x), f (τ x), h01, h02, h12, rfl⟩
  have hScard : S.card = 3 := hcubic.1 x
  have heq : {f x, f (σ x), f (τ x)} = S :=
    Finset.eq_of_subset_of_card_le hsmall (by omega)
  constructor
  · intro hy
    have hyS : y ∈ S := by simpa [S, D] using hy
    rw [← heq] at hyS
    simpa using hyS
  · intro hy
    have hyS : y ∈ ({f x, f (σ x), f (τ x)} : Finset Xm) := by
      simpa using hy
    rw [heq] at hyS
    simpa [S, D] using hyS

/-- Generic normalized collision rule. Here `a` and `b` select any two of
the three matching positions, and `oa`, `ob` are their owner maps. An owner
collision forces the second selected index into the three-element
cross-nondefect neighbourhood of the first source. -/
theorem orderSixtyFour_sizeTwo_muNegThree_cross_owner_collision_index
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (s : V → ℤ)
    (f : MuNegThreePositiveShore (secondOrderDefectGraph G) c s ≃
      MuNegThreeNegativeShore (secondOrderDefectGraph G) c s)
    (σ τ : Equiv.Perm
      (MuNegThreePositiveShore (secondOrderDefectGraph G) c s))
    (a b : MuNegThreePositiveShore (secondOrderDefectGraph G) c s →
      MuNegThreePositiveShore (secondOrderDefectGraph G) c s)
    (oa ob : MuNegThreePositiveShore (secondOrderDefectGraph G) c s → V)
    (hexhaust : ∀ x y, ¬ (secondOrderDefectGraph G).Adj x.1 y.1 ↔
      y = f x ∨ y = f (σ x) ∨ y = f (τ x))
    (hoa : ∀ x z, (G.Adj x.1 z ∧ G.Adj (f (a x)).1 z) ↔ z = oa x)
    (hob : ∀ x z, (G.Adj x.1 z ∧ G.Adj (f (b x)).1 z) ↔ z = ob x)
    {x x' : MuNegThreePositiveShore (secondOrderDefectGraph G) c s}
    (howner : oa x = ob x') :
    b x' = x ∨ b x' = σ x ∨ b x' = τ x := by
  have hax := (hoa x (oa x)).2 rfl
  have hbx := (hob x' (ob x')).2 rfl
  rw [← howner] at hbx
  have hcross :=
    (orderSixtyFour_sizeTwo_muNegThree_cross_owner_rectangle
      G hfree c s x x' (f (a x)) (f (b x')) (oa x) hax hbx).1
  rcases (hexhaust x (f (b x'))).mp hcross with h | h | h
  · exact Or.inl (f.injective h)
  · exact Or.inr (Or.inl (f.injective h))
  · exact Or.inr (Or.inr (f.injective h))

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegThree_cross_owner_rectangle
#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegThree_cross_nondefect_permutationExhaustion
#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegThree_cross_owner_collision_index
