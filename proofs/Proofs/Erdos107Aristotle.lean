/-
  Aristotle targets for Erdős Problem #107 (Happy Ending Problem)
  Routine supporting lemmas for automated proof search.
  See Erdos107Problem.lean for the main formalization.

  These lemmas provide structural support for the formalization of
  the Happy Ending problem (f(n) = minimum points for convex n-gon).

  Suitable for Aristotle:
  - cardSet_three_lower_bound: any m ∈ CardSet 3 satisfies 3 ≤ m
    (structural: a convex 3-gon requires ≥ 3 points, so any configuration
     witnessing 3-gon membership must have at least 3 points)
  - f_3_lb: f 3 ≥ 3 (directly from ersz_lower_bound axiom + norm_num)
-/
import Mathlib
import Proofs.Erdos107Problem

namespace Erdos107.Aristotle

open Erdos107 Finset

/-- Any m in CardSet 3 satisfies 3 ≤ m.
    Proof: if m < 3, take any m-point GP set. Its subsets have card < 3,
    so no 3-element subset T ⊆ pts can exist, contradicting HasConvexNGon 3.
    Routine: uses Finset.card_le_card and omega. -/
theorem cardSet_three_lower_bound : ∀ m ∈ CardSet 3, 3 ≤ m := by
  intro m hm
  -- ersz_lower_bound at n=3: 2^(3-2)+1 = 3 ≤ f 3 = sInf (CardSet 3) ≤ m
  have h3 : 3 ≤ f 3 := by
    have := ersz_lower_bound 3 (by norm_num)
    norm_num at this ⊢
    exact this
  exact le_trans h3 (Nat.sInf_le hm)

/-- Lower bound: 3 ≤ f 3.
    Direct corollary of the Erdős-Szekeres lower bound axiom at n=3:
    2^(3-2) + 1 = 2 + 1 = 3. -/
theorem f_3_lb : 3 ≤ f 3 := by
  have := ersz_lower_bound 3 (by norm_num)
  norm_num at this ⊢
  exact this

/-- HasConvexNGon 3 requires the ambient set to have card ≥ 3. -/
lemma hasConvexNGon_three_card_ge {S : Finset (EuclideanSpace ℝ (Fin 2))}
    (h : HasConvexNGon 3 S) : 3 ≤ S.card := by
  obtain ⟨T, hTS, ⟨hcard, _⟩⟩ := h
  calc 3 = T.card := hcard.symm
    _ ≤ S.card := Finset.card_le_card hTS

/-- Any m-point GP set with m < 3 cannot contain a convex 3-gon.
    Routine: card bound argument. -/
lemma no_convex_ngon_of_lt {S : Finset (EuclideanSpace ℝ (Fin 2))}
    (hcard : S.card < 3) : ¬HasConvexNGon 3 S := by
  intro h
  exact Nat.not_le.mpr hcard (hasConvexNGon_three_card_ge h)

end Erdos107.Aristotle
