/-
  Knight's Tour Oblique Angles: Reversal is Fixed-Point-Free, so the Reversal
  Factor Contributes an Unconditional Factor of 2 (OQ-02, Target E)

  The sibling files built the order-16 symmetry group `D4 × C2` acting on closed
  knight's tours (`KnightsTourObliqueOQ02Order16.lean`), where the `C2` factor is
  time reversal `reverseTour`. The `Order16` file's orbit-divisibility result
  `fullOrbit_card_dvd_sixteen` shows every orbit has size dividing 16, but the
  precise power of 2 dividing `obliqueDistribution k` was left conditional on a
  fixed-point analysis (flagged as the next step in the OQ-02 knowledge trail:
  *"Show closed knight tours are never palindromic … would give every reversal
  orbit size 2, hence 2 ∣ levelSet card unconditionally"*).

  This file closes that gap for the **reversal factor**:

  ## What this file proves (verified, 0 sorries, 0 axioms)

  * `reverseTour_ne_self` — **no closed tour is palindromic**: `reverseTour t ≠ t`.
    A closed tour is a `Nodup` list of 64 distinct squares, and a `Nodup` list
    of length `≥ 2` can never equal its own reverse (its first and last entries
    would coincide). So reversal is a *fixed-point-free* involution on
    `ClosedTour`.
  * `reverseOrbit_card` — every pure reversal orbit `{t, reverseTour t}` has
    cardinality exactly `2` (immediate from fixed-point-freeness).
  * `even_card_levelSet` / `two_dvd_obliqueDistribution` — **the headline**:
    because the fixed-point-free involution `reverseTour` maps every histogram
    level set `levelSet k` bijectively onto itself
    (`levelSet_image_reverseTour_eq`), each level set partitions into matched
    two-element reversal orbits, so `2 ∣ obliqueDistribution k` for **every** `k`,
    unconditionally. This is the reversal analogue of the (conditional) D4 orbit
    count, and it holds with no self-symmetry hypothesis precisely because
    reversal — unlike a board symmetry — can never fix a tour.

  Parent: `KnightsTourOblique.lean`.
  Siblings: `KnightsTourObliqueOQ02.lean`, `…OQ02Reverse.lean`,
  `…OQ02ReverseCount.lean`, `…OQ02Order16.lean`.
-/

import Mathlib
import Proofs.KnightsTourObliqueOQ02Order16

namespace KnightsTourOblique

open List

/-! ## A `Nodup` list of length ≥ 2 cannot be a palindrome -/

/-- A `Nodup` list that equals its own reverse has length at most one. If it had
    length `≥ 2`, its entry at index `length - 1` would equal its entry at index
    `0` (reversal swaps them), contradicting `Nodup`. -/
private theorem nodup_reverse_eq_length_le_one {α : Type*} {l : List α}
    (hnd : l.Nodup) (hrev : l.reverse = l) : l.length ≤ 1 := by
  by_contra hlt
  push_neg at hlt
  -- `hlt : 1 < l.length`, so indices `0` and `l.length - 1` are valid and distinct.
  -- The reversed list's entry at `0` is the original's entry at `l.length - 1 - 0`;
  -- rewriting `l.reverse = l` identifies it with the entry at `0`.
  have e : l[l.length - 1 - 0]'(by omega) = l[0]'(by omega) := by
    rw [← List.getElem_reverse]
    · simp only [hrev]
    · rw [List.length_reverse]; omega
  have hidx : l.length - 1 - 0 = 0 := (List.Nodup.getElem_inj_iff hnd).mp e
  omega

/-! ## Reversal is fixed-point-free -/

/-- **No closed knight's tour is palindromic.** A `ClosedTour` is a `Nodup` list
    of 64 squares, and a `Nodup` list of length `≥ 2` cannot equal its own
    reverse, so `reverseTour t ≠ t`. Hence time reversal is a fixed-point-free
    involution on `ClosedTour`. -/
theorem reverseTour_ne_self (t : ClosedTour) : reverseTour t ≠ t := by
  intro h
  have hpal : t.squares.reverse = t.squares := by
    have h' := (closedTour_eq_iff (reverseTour t) t).mp h
    rwa [reverseTour_squares] at h'
  have hle := nodup_reverse_eq_length_le_one t.nodup hpal
  rw [t.length_eq] at hle
  omega

/-- Every pure reversal orbit `{t, reverseTour t}` has exactly two elements,
    because reversal fixes no tour. -/
theorem reverseOrbit_card (t : ClosedTour) :
    ({t, reverseTour t} : Finset ClosedTour).card = 2 :=
  Finset.card_pair (reverseTour_ne_self t).symm

/-! ## A fixed-point-free involution forces even cardinality

`even_card_of_fpf_involution` is a general helper (also used in
`SzemerediRegularityOQ01.lean`); it is re-proved here so this file stays
self-contained. -/

/-- **A fixed-point-free involution forces even cardinality.** If `σ : α → α`
    maps `S` to itself, is an involution on `S`, and has no fixed point on `S`,
    then `S` splits into two-element orbits `{x, σ x}`, so `S.card` is even.
    Proved by strong induction, removing one orbit at a time. -/
private theorem even_card_of_fpf_involution {α : Type*} [DecidableEq α]
    {S : Finset α} {σ : α → α}
    (hσ_mem : ∀ x ∈ S, σ x ∈ S)
    (hσ_inv : ∀ x ∈ S, σ (σ x) = x)
    (hσ_ne : ∀ x ∈ S, σ x ≠ x) :
    Even S.card := by
  induction S using Finset.strongInduction with
  | H S ih =>
    by_cases hS : S = ∅
    · subst hS; exact ⟨0, by simp⟩
    · obtain ⟨a, ha⟩ := Finset.nonempty_of_ne_empty hS
      have hσa_ne : σ a ≠ a := hσ_ne a ha
      have hpair_sub : {a, σ a} ⊆ S := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx'
        · exact ha
        · rw [Finset.mem_singleton] at hx'; subst hx'; exact hσ_mem a ha
      have hmem : ∀ x, x ∈ S \ {a, σ a} ↔ x ∈ S ∧ x ≠ a ∧ x ≠ σ a := fun x => by
        rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or]
      have hT_mem : ∀ x ∈ S \ {a, σ a}, σ x ∈ S \ {a, σ a} := by
        intro x hx
        rw [hmem] at hx ⊢
        refine ⟨hσ_mem x hx.1, ?_, ?_⟩
        · intro heq; apply hx.2.2; rw [← hσ_inv x hx.1, heq]
        · intro heq; apply hx.2.1; rw [← hσ_inv x hx.1, heq, hσ_inv a ha]
      have hT_inv : ∀ x ∈ S \ {a, σ a}, σ (σ x) = x :=
        fun x hx => hσ_inv x (Finset.mem_sdiff.mp hx).1
      have hT_ne : ∀ x ∈ S \ {a, σ a}, σ x ≠ x :=
        fun x hx => hσ_ne x (Finset.mem_sdiff.mp hx).1
      have hsub : S \ {a, σ a} ⊆ S := Finset.sdiff_subset
      have hT_lt : S \ {a, σ a} ⊂ S := by
        rw [Finset.ssubset_iff_of_subset hsub]
        exact ⟨a, ha, by simp⟩
      obtain ⟨k, hk⟩ := ih (S \ {a, σ a}) hT_lt hT_mem hT_inv hT_ne
      have hcard_pair : ({a, σ a} : Finset α).card = 2 :=
        Finset.card_pair hσa_ne.symm
      have h2 : 2 ≤ S.card := by
        rw [← hcard_pair]; exact Finset.card_le_card hpair_sub
      have hcard : (S \ {a, σ a}).card = S.card - 2 := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hpair_sub, hcard_pair]
      rw [hcard] at hk
      exact ⟨k + 1, by omega⟩

/-! ## The reversal factor of 2 in the histogram, unconditionally -/

/-- **Every histogram level set has even cardinality.** Time reversal is a
    fixed-point-free involution (`reverseTour_ne_self`, `reverseTour_involutive`)
    that maps `levelSet k` into itself (`levelSet_image_reverseTour_eq`), so the
    level set splits into two-element reversal orbits and its cardinality is
    even. -/
theorem even_card_levelSet (k : ℕ) : Even (levelSet k).card := by
  apply even_card_of_fpf_involution (σ := reverseTour)
  · -- reversal maps `levelSet k` into itself
    intro t ht
    have : reverseTour t ∈ (levelSet k).image reverseTour :=
      Finset.mem_image_of_mem _ ht
    rwa [levelSet_image_reverseTour_eq] at this
  · exact fun t _ => reverseTour_involutive t
  · exact fun t _ => reverseTour_ne_self t

/-- **The reversal factor of 2 in the oblique histogram (headline).** For every
    `k`, `2 ∣ obliqueDistribution k` — unconditionally, with no self-symmetry
    hypothesis. This holds because reversal, unlike a board symmetry, can never
    fix a tour, so it pairs the tours in each level set two-by-two. -/
theorem two_dvd_obliqueDistribution (k : ℕ) : 2 ∣ obliqueDistribution k := by
  rw [obliqueDistribution_eq_levelSet_card]
  exact (even_card_levelSet k).two_dvd

end KnightsTourOblique
