import Proofs.Erdos85ThreeSeparatorUniformRFiberDeviation

/-!
# Overlap ledger for the uniform R-fiber design

In the future intersection graph `Γ_R`, edges are labeled by `C \ U_P`.
The B36 hole set is `U_P \ C`.  Their cardinalities are determined solely
by `|C|=a` and `|U_P|=3a`: overlap is at most `a`, and holes are the
baseline `2a` plus one per overlap.  This is the numerical part of (B37).
-/

open Finset

namespace Erdos85

noncomputable section

/-- Exact B37 overlap/hole cardinality ledger. -/
theorem uniform_Rfiber_overlap_hole_ledger
    {V : Type*} [DecidableEq V]
    (C U : Finset V) (a : ℕ)
    (hCcard : C.card = a)
    (hUcard : U.card = 3 * a) :
    (C \ U).card = a - (C ∩ U).card ∧
      (C \ U).card ≤ a ∧
      (U \ C).card = 2 * a + (C \ U).card := by
  have hCsplit := Finset.card_sdiff_add_card_inter C U
  have hsurplus := uniform_Rfiber_hole_surplus C U a hCcard hUcard
  rw [hCcard] at hCsplit
  constructor
  · omega
  constructor
  · omega
  · omega

/-- If an intersection graph has one edge for each point of `C \ U`, the
same ledger immediately bounds its edge count and identifies the holes. -/
theorem uniform_Rfiber_intersectionGraph_card_ledger
    {V E : Type*} [DecidableEq V] [Fintype E]
    (C U : Finset V) (a : ℕ)
    (hCcard : C.card = a)
    (hUcard : U.card = 3 * a)
    (hedges : Fintype.card E = (C \ U).card) :
    Fintype.card E ≤ a ∧
      (U \ C).card = 2 * a + Fintype.card E := by
  have hledger := uniform_Rfiber_overlap_hole_ledger C U a hCcard hUcard
  omega

end

end Erdos85

#print axioms Erdos85.uniform_Rfiber_overlap_hole_ledger
#print axioms Erdos85.uniform_Rfiber_intersectionGraph_card_ledger
