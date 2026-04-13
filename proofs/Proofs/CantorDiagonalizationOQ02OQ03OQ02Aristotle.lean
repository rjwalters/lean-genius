/-
  Aristotle targets for CantorDiagonalizationOQ02OQ03OQ02 (Fodor's Pressing-Down Lemma)
  Routine supporting lemmas for automated proof search.
  See CantorDiagonalizationOQ02OQ03OQ02.lean for the main formalization.

  Status: 1 sorry remaining — diagInter_isUnbounded

  The sorry is the "unbounded" half of: the diagonal intersection of a
  κ-indexed family of clubs is a club. The "closed" half is already proved.

  Proof strategy for diagInter_isUnbounded:
    Given α₀ < κ.ord, find β ∈ diagInter f with α₀ < β < κ.ord.
    Build an ω-sequence by induction:
      α_{n+1} ∈ ⋂_{β ≤ α_n} f(β) with α_n < α_{n+1} < κ.ord
    Let α_ω = iSup(n, α_n). Then:
    (a) α_ω < κ.ord: ℕ-many terms, each < κ.ord, and κ is regular
        → Ordinal.iSup_lt_ord applies
    (b) α_ω ∈ diagInter f: for any β < α_ω, pick n with β ≤ α_n;
        then α_m for m > n are all in f(β) and increase to α_ω;
        since f(β) is closed and α_ω is their limit, α_ω ∈ f(β).

  Helper lemmas:
  1. isClub_inter: finite intersection of clubs is a club
  2. diagInter_isUnbounded_ari: the main sorry (exposed for Aristotle)
-/
import Mathlib
import Proofs.CantorDiagonalizationOQ02OQ03OQ02

namespace FodorLemmaAristotle

open FodorLemma Cardinal Ordinal

/-- The intersection of two clubs below κ.ord is itself a club.
    Both components (unbounded and closed) pass to the intersection. -/
lemma isClub_inter {κ : Cardinal} (hκ : κ.IsRegular) (hκ_unc : ℵ₀ < κ)
    {C₁ C₂ : Set Ordinal}
    (hC₁ : IsClub κ C₁) (hC₂ : IsClub κ C₂) :
    IsClub κ (C₁ ∩ C₂) := by
  sorry

/-- The diagonal intersection of a κ-indexed family of clubs is unbounded
    below κ.ord. This is the main sorry in the parent file. -/
lemma diagInter_isUnbounded_ari {κ : Cardinal} (hκ : κ.IsRegular) (hκ_unc : ℵ₀ < κ)
    {f : Ordinal → Set Ordinal} (hf : ∀ β, β < κ.ord → IsClub κ (f β)) :
    IsUnboundedBelow κ (diagInter f) := by
  sorry

end FodorLemmaAristotle
