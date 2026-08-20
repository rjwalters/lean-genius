import Proofs.Erdos85MuNegThreeZeroFiveCorrectShoreGeometry
import Proofs.Erdos85EdgeIndexedServiceIndependentEigenvectors

/-! # Kernel of endpoint summation in corrected h305 shores -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

theorem edgeEndpointSumVector_apply
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (f : V → ℂ) (a : R.edgeFinset) :
    edgeEndpointSumVector R f a = ∑ x ∈ a.1.toFinset, f x := by
  classical
  unfold edgeEndpointSumVector
  simp only [Matrix.mulVec, dotProduct, edgeEndpointIncidenceMatrix,
    Matrix.transpose_apply]
  simp only [ite_mul, one_mul, zero_mul]
  change (∑ x ∈ (Finset.univ : Finset V),
    if x ∈ a.1.toFinset then f x else 0) = _
  rw [← Finset.sum_filter]
  have heq : (Finset.univ.filter fun x : V ↦ x ∈ a.1.toFinset) =
      a.1.toFinset := by
    ext x
    simp
  rw [heq]

/-- Endpoint summation has trivial kernel on either corrected h305 shore.
The antipodal edge negates values, whereas four successive odd-offset edges
preserve them, forcing zero. -/
theorem h305_correctShoreMode_endpointSum_kernel
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (u : ZMod 8 → V) (huinj : Function.Injective u)
    (f : V → ℂ)
    (hker : edgeEndpointSumVector R f = 0)
    (hmode : MuNegThreeZeroFiveTriangleShoreMode R u ∨
      MuNegThreeZeroFiveTfShoreMode R u) :
    ∀ i, f (u i) = 0 := by
  classical
  have hneg (i j : ZMod 8) (hij : i ≠ j) (hadj : R.Adj (u i) (u j)) :
      f (u j) = -f (u i) := by
    let a : R.edgeFinset := ⟨s(u i, u j), R.mem_edgeFinset.mpr hadj⟩
    have hz := congrFun hker a
    rw [Pi.zero_apply, edgeEndpointSumVector_apply] at hz
    have hpair : a.1.toFinset = {u i, u j} := by
      exact Sym2.toFinset_mk_eq
    rw [hpair, Finset.sum_pair (huinj.ne hij)] at hz
    linear_combination hz
  have hne (i : ZMod 8) (d : ZMod 8) (hd : d ≠ 0) : i ≠ i + d := by
    intro h
    have hz := congrArg (fun z ↦ z - i) h
    simp at hz
    exact hd hz.symm
  intro i
  rcases hmode with htri | htf
  · have h1 (q : ZMod 8) : f (u (q + 1)) = -f (u q) := by
      apply hneg q (q + 1) (hne q 1 (by decide))
      apply (htri q (q + 1)).mpr
      left
      ring
    have h4 : f (u (i + 4)) = -f (u i) := by
      apply hneg i (i + 4) (hne i 4 (by decide))
      apply (htri i (i + 4)).mpr
      exact Or.inr (Or.inl (by ring))
    have h0 := h1 i
    have h1' := h1 (i + 1)
    have h2 := h1 (i + 2)
    have h3 := h1 (i + 3)
    ring_nf at h0 h1' h2 h3 h4
    linear_combination (h0 - h1' + h2 - h3 + h4) / 2
  · have h3step (q : ZMod 8) : f (u (q + 3)) = -f (u q) := by
      apply hneg q (q + 3) (hne q 3 (by decide))
      apply (htf q (q + 3)).mpr
      left
      ring
    have h4 : f (u (i + 4)) = -f (u i) := by
      apply hneg i (i + 4) (hne i 4 (by decide))
      apply (htf i (i + 4)).mpr
      exact Or.inr (Or.inl (by ring))
    have h0 := h3step i
    have h1' := h3step (i + 3)
    have h2 := h3step (i + 6)
    have h3 := h3step (i + 9)
    ring_nf at h0 h1' h2 h3 h4
    have h12 : (12 : ZMod 8) = 4 := by decide
    rw [h12] at h3
    linear_combination (h0 - h1' + h2 - h3 + h4) / 2

end

end Erdos85

#print axioms Erdos85.h305_correctShoreMode_endpointSum_kernel
