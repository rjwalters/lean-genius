import Proofs.Erdos85MuNegThreeZeroFiveEndpointSumKernel

/-! # Global injectivity of endpoint summation in the h305 two-shore case -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- Corrected h305 modes on two C8 shores covering the support make endpoint
summation globally injective. -/
theorem h305_two_correctShoreModes_endpointSum_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (u v : ZMod 8 → V)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hcover : ∀ x : V, (∃ i, x = u i) ∨ ∃ j, x = v j)
    (hmodeu : MuNegThreeZeroFiveTriangleShoreMode R u ∨
      MuNegThreeZeroFiveTfShoreMode R u)
    (hmodev : MuNegThreeZeroFiveTriangleShoreMode R v ∨
      MuNegThreeZeroFiveTfShoreMode R v) :
    Function.Injective (edgeEndpointSumVector R) := by
  intro f g hfg
  have hker : edgeEndpointSumVector R (f - g) = 0 := by
    unfold edgeEndpointSumVector
    rw [Matrix.mulVec_sub]
    change (edgeEndpointIncidenceMatrix R).transpose.mulVec f =
      (edgeEndpointIncidenceMatrix R).transpose.mulVec g at hfg
    rw [hfg, sub_self]
  have hu := h305_correctShoreMode_endpointSum_kernel
    R u huinj (f - g) hker hmodeu
  have hv := h305_correctShoreMode_endpointSum_kernel
    R v hvinj (f - g) hker hmodev
  funext x
  rcases hcover x with ⟨i, rfl⟩ | ⟨j, rfl⟩
  · exact sub_eq_zero.mp (hu i)
  · exact sub_eq_zero.mp (hv j)

/-- Equivalence-coordinate form of the global injectivity theorem. -/
theorem h305_equiv_correctShoreModes_endpointSum_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (e : (ZMod 8 ⊕ ZMod 8) ≃ V)
    (hmodeu : MuNegThreeZeroFiveTriangleShoreMode R
        (fun i ↦ e (Sum.inl i)) ∨
      MuNegThreeZeroFiveTfShoreMode R (fun i ↦ e (Sum.inl i)))
    (hmodev : MuNegThreeZeroFiveTriangleShoreMode R
        (fun j ↦ e (Sum.inr j)) ∨
      MuNegThreeZeroFiveTfShoreMode R (fun j ↦ e (Sum.inr j))) :
    Function.Injective (edgeEndpointSumVector R) := by
  apply h305_two_correctShoreModes_endpointSum_injective R
    (fun i ↦ e (Sum.inl i)) (fun j ↦ e (Sum.inr j))
  · exact e.injective.comp Sum.inl_injective
  · exact e.injective.comp Sum.inr_injective
  · intro x
    obtain ⟨i | j, rfl⟩ := e.surjective x
    · exact Or.inl ⟨i, rfl⟩
    · exact Or.inr ⟨j, rfl⟩
  · exact hmodeu
  · exact hmodev

/-- Hence endpoint summation preserves every linearly independent family,
not merely the two explicit alternating modes. -/
theorem h305_correctShoreModes_endpointSum_preserves_linearIndependent
    {V ι : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (u v : ZMod 8 → V)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hcover : ∀ x : V, (∃ i, x = u i) ∨ ∃ j, x = v j)
    (hmodeu : MuNegThreeZeroFiveTriangleShoreMode R u ∨
      MuNegThreeZeroFiveTfShoreMode R u)
    (hmodev : MuNegThreeZeroFiveTriangleShoreMode R v ∨
      MuNegThreeZeroFiveTfShoreMode R v)
    (f : ι → V → ℂ) (hli : LinearIndependent ℂ f) :
    LinearIndependent ℂ (fun i ↦ edgeEndpointSumVector R (f i)) := by
  let L : (V → ℂ) →ₗ[ℂ] (R.edgeFinset → ℂ) := {
    toFun := edgeEndpointSumVector R
    map_add' := by
      intro p q
      unfold edgeEndpointSumVector
      exact Matrix.mulVec_add _ _ _
    map_smul' := by
      intro c p
      unfold edgeEndpointSumVector
      exact Matrix.mulVec_smul _ _ _ }
  have hinj : Function.Injective L := by
    simpa [L] using
      (h305_two_correctShoreModes_endpointSum_injective R u v huinj hvinj
        hcover hmodeu hmodev)
  have hmap := hli.map' L (LinearMap.ker_eq_bot.mpr hinj)
  simpa [L, Function.comp_def] using hmap

end

end Erdos85

#print axioms Erdos85.h305_two_correctShoreModes_endpointSum_injective
#print axioms Erdos85.h305_equiv_correctShoreModes_endpointSum_injective
#print axioms
  Erdos85.h305_correctShoreModes_endpointSum_preserves_linearIndependent
