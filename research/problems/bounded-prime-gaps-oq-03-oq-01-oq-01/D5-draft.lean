/-
  DRAFT SKELETON (NOT registered, NOT in Proofs.lean — zero build-gate risk).
  bounded-prime-gaps-oq-03-oq-01-oq-01 — D(5) = 12 from scratch.

  OBSERVE-phase draft (researcher-1, S1, 2026-06-16). Authored under DUAL
  BLACKOUT (Docker `docker run` hangs exit 124; Aristotle MCP `prove` 404), so
  UNVERIFIED. Mirrors the parent's `minAdmissibleDiameter_2` /
  `minAdmissibleDiameter_3` proof shape (`BoundedPrimeGapsOQ03OQ01.lean:173/188`).

  Two load-bearing obligations:
    (1) `admissible_5tuple_0_2_6_8_12` — witness admissibility (easy; copy the
        `admissible_quadruple_0_2_6_8` shape, line 165 of the parent).
    (2) `admissible_5tuple_diam_ge_12` — the lower bound (the real content).
        Strategy: translation-invariance to fix min = 0, then a finite
        `native_decide` over the 5-subsets of {0,…,11} containing 0, each
        inadmissible mod 2 or mod 3.

  On a Docker-up worktree: build this file; if green, transcribe into a new
  registered `Proofs/BoundedPrimeGapsOQ03OQ01OQ01.lean` (or fold into the parent
  next to D(2)/D(3)).
-/
import Mathlib
import Proofs.BoundedPrimeGaps
import Proofs.BoundedPrimeGapsOQ03OQ01

namespace BoundedPrimeGapsOQ03OQ01OQ01

open Nat Finset BoundedPrimeGaps BoundedPrimeGapsOQ03OQ01

/-- Witness admissibility: `{0, 2, 6, 8, 12}` is admissible (diameter 12).
    Only p ∈ {2,3,5} can possibly cover a 5-set; none does (residues miss a
    class), and p ≥ 7 cannot cover 5 < 7 points. `decide`/`native_decide` over
    the `IsAdmissible` predicate, exactly as `admissible_quadruple_0_2_6_8`. -/
theorem admissible_5tuple_0_2_6_8_12 :
    IsAdmissible ({0, 2, 6, 8, 12} : Finset ℕ) := by
  sorry  -- copy admissible_quadruple_0_2_6_8 shape (parent line 165)

/-- **Lower bound — the real content.** Every admissible 5-tuple has diameter
    ≥ 12. By translation-invariance assume `min = 0`; then `H ⊆ {0,…,11}` would
    force a covering mod 2 or mod 3 (finite `native_decide`). -/
theorem admissible_5tuple_diam_ge_12
    (H : Finset ℕ) (hcard : H.card = 5) (hadm : IsAdmissible H) :
    12 ≤ fsDiameter H := by
  sorry  -- LOAD-BEARING: shift to min=0 + native_decide over 5-subsets of {0..11}

/-- D(5) = 12. Same `le_antisymm` assembly as `minAdmissibleDiameter_3`. -/
theorem minAdmissibleDiameter_5 : minAdmissibleDiameter 5 = 12 := by
  apply le_antisymm
  · -- Upper: {0,2,6,8,12} witnesses D(5) ≤ 12
    apply csInf_le ⟨0, fun _ _ => Nat.zero_le _⟩
    exact ⟨{0, 2, 6, 8, 12}, by decide, admissible_5tuple_0_2_6_8_12, by native_decide⟩
  · -- Lower: every admissible 5-tuple has diameter ≥ 12
    have hne : Set.Nonempty
        {d | ∃ H : Finset ℕ, H.card = 5 ∧ IsAdmissible H ∧ fsDiameter H = d} :=
      ⟨12, {0, 2, 6, 8, 12}, by decide, admissible_5tuple_0_2_6_8_12, by native_decide⟩
    apply le_csInf hne
    rintro d ⟨H, hcard, hadm, rfl⟩
    exact admissible_5tuple_diam_ge_12 H hcard hadm

end BoundedPrimeGapsOQ03OQ01OQ01
