import Proofs.Erdos85ThreeSeparatorExceptionalPointYCompositeFixedLocus
import Proofs.Erdos85ThreeSeparatorPositiveSpikeLocationParity

/-!
# Cardinality of the large-shore composite fixed locus

At the endpoint, B16a makes the K-section of `X` even, while B16 bounds it
by three.  Together with B17Y''' this leaves exactly zero or two fixed
points.  This is B17Y''''.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Arithmetic core of B17Y''''. -/
theorem even_le_three_eq_zero_or_two
    {n : ℕ} (heven : Even n) (hle : n ≤ 3) : n = 0 ∨ n = 2 := by
  obtain ⟨k, hk⟩ := heven
  omega

/-- Finset consumer: an even K-section of size at most three gives a
zero-or-two composite fixed locus. -/
theorem exceptionalPoint_Y_fixedLocus_card_eq_zero_or_two
    {V : Type*} [DecidableEq V]
    (X K : Finset V) (θ : V → V)
    (hfixed : X.filter (fun x ↦ θ x = x) = K ∩ X)
    (heven : Even (X ∩ K).card)
    (hsmall : (K ∩ X).card ≤ 3) :
    (X.filter (fun x ↦ θ x = x)).card = 0 ∨
      (X.filter (fun x ↦ θ x = x)).card = 2 := by
  have heven' : Even (K ∩ X).card := by
    simpa [Finset.inter_comm] using heven
  rw [hfixed]
  exact even_le_three_eq_zero_or_two heven' hsmall

/-- Graph-facing endpoint B17Y'''': derive the parity input directly from
the endpoint internal-degree indicator profile. -/
theorem exceptionalPoint_Y_endpoint_fixedLocus_card_eq_zero_or_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (X K : Finset V) (θ : V → V)
    (hXeven : Even X.card)
    (hprofile : ∀ x ∈ X,
      (A.neighborFinset x ∩ X).card + (if x ∈ K then 1 else 0) = 1)
    (hfixed : X.filter (fun x ↦ θ x = x) = K ∩ X)
    (hsmall : (K ∩ X).card ≤ 3) :
    (X.filter (fun x ↦ θ x = x)).card = 0 ∨
      (X.filter (fun x ↦ θ x = x)).card = 2 := by
  have heven := even_card_inter_of_even_shore_internal_indicator_profile
    A X K 0 hXeven (by simpa using hprofile)
  exact exceptionalPoint_Y_fixedLocus_card_eq_zero_or_two
    X K θ hfixed heven hsmall

end

end Erdos85

#print axioms Erdos85.even_le_three_eq_zero_or_two
#print axioms Erdos85.exceptionalPoint_Y_fixedLocus_card_eq_zero_or_two
#print axioms Erdos85.exceptionalPoint_Y_endpoint_fixedLocus_card_eq_zero_or_two
