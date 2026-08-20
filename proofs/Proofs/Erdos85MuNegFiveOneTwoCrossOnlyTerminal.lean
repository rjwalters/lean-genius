import Proofs.Erdos85NegativeOrbitAssembly
import Proofs.Erdos85MuNegFiveOneTwoCrossOnlyGraphRealization

/-! # Callback-ready corrected h512 terminal -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- Direct and once-transported h512 endpoints are both discharged by the
corrected 64-owner graph certificate. -/
theorem false_of_h512_source_or_transported
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (hc : c.supp.ncard = 8 * 2)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)}) :
    let K := (secondOrderDefectGraph G).induce c.supp
    let N₁ : Matrix (ZMod 8) (ZMod 8) ℤ :=
      fun i j ↦ K.adjMatrix ℤ (u i) (u j)
    let N₂ : Matrix (ZMod 8) (ZMod 8) ℤ :=
      fun i j ↦ K.adjMatrix ℤ (v i) (v j)
    Nonempty (NegativeEightEightSourceWitness G c a b N₁ N₂ (-5) 1 2) ∨
      NegativeEightEightTransportedWitness G c a N₁ N₂ (-5) 1 2 →
    False := by
  classical
  dsimp only
  let K := (secondOrderDefectGraph G).induce c.supp
  let N₁ : Matrix (ZMod 8) (ZMod 8) ℤ :=
    fun i j ↦ K.adjMatrix ℤ (u i) (u j)
  let M₁ : Matrix (ZMod 8) (ZMod 8) ℤ :=
    fun i j ↦ K.adjMatrix ℤ (u i) (v j)
  let N₂ : Matrix (ZMod 8) (ZMod 8) ℤ :=
    fun i j ↦ K.adjMatrix ℤ (v i) (v j)
  let M₂ : Matrix (ZMod 8) (ZMod 8) ℤ :=
    fun i j ↦ K.adjMatrix ℤ (v i) (u j)
  intro h
  obtain ⟨s, _hs, _hcell, _hmode₁, _hmode₂, L₁, L₂⟩ :=
    exists_muNegFive_exact_data_of_source_or_transported
      G hfree hreg hcard c hc a b hab u v huinj hvinj hurange hvrange
        hu hv 1 2 (by omega) h
  let su : ZMod 8 → ℤ := fun i ↦ s (u i).1
  let sv : ZMod 8 → ℤ := fun j ↦ s (v j).1
  have hphase := zmodEight_two_alternating_sign_phase_routing
    su sv L₁.f_sign L₁.g_sign L₁.f_flip L₁.g_flip
  apply muNegFiveOneTwoCrossOnly_graph_false
    G c a b u v hfree hreg hcard hc hab huinj hvinj hurange hvrange
      hu hv s (muNegOneSigmaOf su sv)
  · intro x y hx hy
    have hp := muNegOneSigma_coherence su sv L₁.f_sign L₁.g_sign
      hphase x y hx hy
    have hb : muNegFiveZeroThreeSameSign (muNegOneSigmaOf su sv) x y =
        (muNegOneSign (muNegOneSigmaOf su sv) x ==
          muNegOneSign (muNegOneSigmaOf su sv) (8 + y)) := by
      generalize muNegOneSigmaOf su sv = sigma
      cases sigma <;> interval_cases x <;> interval_cases y <;> decide
    rw [hb]
    exact ⟨fun hs ↦ (hp.mpr hs).symm, fun hs ↦ hp.mp hs.symm⟩
  · simpa [su, sv, N₁, M₁, K] using L₁
  · simpa [su, sv, N₂, M₂, K] using L₂

end

end Erdos85

#print axioms Erdos85.false_of_h512_source_or_transported
