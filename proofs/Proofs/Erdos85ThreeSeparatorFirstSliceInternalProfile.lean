import Proofs.Erdos85ThreeSeparatorPositiveSpikeLocationParity

/-!
# Internal graph profile on the first non-endpoint slice

At `a=1`, the positive-spike profile reads
`deg_{A[X]}(x) + 1_K(x) = 2`.  Thus the internal graph has maximum degree
two and its degree-one locus is exactly `K ∩ X`.  This is the local-degree
interface for the path/cycle decomposition (B22).
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Pointwise form of the B22 internal-degree profile. -/
theorem firstSlice_internal_degree_le_two_and_eq_one_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (X K : Finset V)
    (hprofile : ∀ x ∈ X,
      (A.neighborFinset x ∩ X).card + (if x ∈ K then 1 else 0) = 2) :
    ∀ x ∈ X,
      (A.neighborFinset x ∩ X).card ≤ 2 ∧
        ((A.neighborFinset x ∩ X).card = 1 ↔ x ∈ K) := by
  intro x hx
  have hp := hprofile x hx
  constructor
  · omega
  constructor
  · intro hone
    by_contra hxK
    simp [hxK] at hp
    omega
  · intro hxK
    simp [hxK] at hp
    omega

/-- Finset form: the degree-one vertices of the graph internal to `X` are
precisely the K-points of `X`. -/
theorem firstSlice_internal_degreeOne_locus
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (X K : Finset V)
    (hprofile : ∀ x ∈ X,
      (A.neighborFinset x ∩ X).card + (if x ∈ K then 1 else 0) = 2) :
    X.filter (fun x ↦ (A.neighborFinset x ∩ X).card = 1) = K ∩ X := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_inter]
  constructor
  · rintro ⟨hx, hone⟩
    exact ⟨(firstSlice_internal_degree_le_two_and_eq_one_iff
      A X K hprofile x hx).2.mp hone, hx⟩
  · rintro ⟨hxK, hx⟩
    exact ⟨hx, (firstSlice_internal_degree_le_two_and_eq_one_iff
      A X K hprofile x hx).2.mpr hxK⟩

end

end Erdos85

#print axioms Erdos85.firstSlice_internal_degree_le_two_and_eq_one_iff
#print axioms Erdos85.firstSlice_internal_degreeOne_locus
