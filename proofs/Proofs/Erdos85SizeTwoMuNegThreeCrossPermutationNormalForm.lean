import Proofs.Erdos85SizeTwoMuNegThreeCrossComplement

/-! # Permutation normal form for the `mu = -3` cross complement -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- After choosing one of the three cross perfect matchings as the shore
identification, the other two become pointwise distinct fixed-point-free
permutations of the positive shore. -/
theorem orderSixtyFour_sizeTwo_muNegThree_cross_nondefect_permutationNormalForm
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
      (∀ x, ¬ D.Adj x.1 (f x).1) ∧
      (∀ x, ¬ D.Adj x.1 (f (σ x)).1) ∧
      (∀ x, ¬ D.Adj x.1 (f (τ x)).1) ∧
      (∀ x, σ x ≠ x) ∧ (∀ x, τ x ≠ x) ∧
      ∀ x, σ x ≠ τ x := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let Xp := MuNegThreePositiveShore D c s
  let Xm := MuNegThreeNegativeShore D c s
  obtain ⟨f, g, k, hf, hg, hk, hfg, hfk, hgk⟩ :=
    orderSixtyFour_sizeTwo_muNegThree_cross_nondefect_threeMatchings
      G hfree hreg hcard c hc s hs_out hs_in hH hD
  let σ : Equiv.Perm Xp := g.trans f.symm
  let τ : Equiv.Perm Xp := k.trans f.symm
  refine ⟨f, σ, τ, hf, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    simpa [σ] using hg x
  · intro x
    simpa [τ] using hk x
  · intro x hσ
    apply hfg x
    have heq : g x = f x := by
      calc
        g x = f (σ x) := by simp [σ]
        _ = f x := congrArg f hσ
    exact heq.symm
  · intro x hτ
    apply hfk x
    have heq : k x = f x := by
      calc
        k x = f (τ x) := by simp [τ]
        _ = f x := congrArg f hτ
    exact heq.symm
  · intro x hστ
    apply hgk x
    calc
      g x = f (σ x) := by simp [σ]
      _ = f (τ x) := congrArg f hστ
      _ = k x := by simp [τ]

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegThree_cross_nondefect_permutationNormalForm
