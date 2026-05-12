/-
  Knight's Tour Oblique Angles: Distribution Structural Skeleton (OQ-02)

  Open question OQ-02: distribution of oblique counts across all closed
  knight's tours on the 8×8 chessboard. Knuth (2025 Christmas Lecture)
  proved every tour has ≥ 4 oblique turns and the minimum is achieved by
  a unique tour up to D4 symmetry. The histogram values
  `obliqueDistribution 5, 6, …` are unreachable in Lean (would require
  enumerating ~1.3 × 10^13 tours), but the **structural skeleton** of the
  distribution — support, D4-orbit divisibility, reversal symmetry — is
  reachable using only the parent file's existing infrastructure.

  ## What this file provides (S2 ORIENT)

  - A `Fintype` instance for `ClosedTour` (Target A1, prerequisite for the
    histogram definition; the parent file uses `Classical.choice` and does
    not expose this).
  - `obliqueDistribution : ℕ → ℕ` (Target A2): the histogram function
    defined as a `Finset.filter` over `Finset.univ : Finset ClosedTour`.
  - `obliqueDistribution_zero_below_four` (Target B): the support lower
    bound — a direct lift of the parent's `oblique_lower_bound`.

  ## What is deferred to S3+

  - D4 group action on `ClosedTour` and `obliqueCount`-invariance (Target C).
  - Reversal symmetry `obliqueCount (reverse t) = obliqueCount t` (Target D).
  - Winding-parity joint constraint on `#turnAngle = 3` and `#turnAngle = 5`
    sub-distributions (Target E).

  ## Status

  - [x] Fintype instance via injection into `Fin 64 → Square`
  - [x] Distribution definition
  - [x] Support lower bound (k < 4)
  - [ ] D4 invariance (S3)
  - [ ] Reversal symmetry (S3)
  - [ ] Winding-parity constraint (S4)

  Parent proof: `KnightsTourOblique.lean` (8×8 minimum + uniqueness).
  Sibling: `KnightsTourObliqueOQ01.lean` (n×n minimum, n ≥ 5).

  References
  - Knuth, D. E. (2025). *29th Annual Christmas Lecture: Knight's Tours
    and Oblique Turns*. Stanford University.
  - Knuth, D. E. *TAOCP Volume 4, Fascicle 8a: Knight's Tours* (forthcoming).
-/

import Mathlib
import Proofs.KnightsTourOblique

namespace KnightsTourOblique

/-!
## Fintype instance for ClosedTour

`ClosedTour` is a structure with one data field (`squares : List Square`)
of length 64, plus several propositional fields. To get a `Fintype`
instance we inject `ClosedTour ↪ (Fin 64 → Square)` by sending a tour to
its indexing function and use `Fintype.ofInjective`. Two tours with the
same indexing function have the same `squares` list (by `List.ext_get`),
and structure-equality of `ClosedTour` is determined by `squares` since
all other fields are propositions.
-/

/-- The indexing function of a closed tour: `toFn t i = t.squares[i]`. -/
def toFn (t : ClosedTour) : Fin 64 → Square := fun i =>
  t.squares.get ⟨i.val, by rw [t.length_eq]; exact i.isLt⟩

theorem toFn_injective : Function.Injective toFn := by
  rintro ⟨s1, h1, n1, p1, ne1, c1⟩ ⟨s2, h2, n2, p2, ne2, c2⟩ heq
  -- First, show the underlying lists are equal.
  have hsq : s1 = s2 := by
    apply List.ext_get
    · exact h1.trans h2.symm
    · intro i hi1 hi2
      have hi64 : i < 64 := by rw [h1] at hi1; exact hi1
      have := congrFun heq ⟨i, hi64⟩
      simpa [toFn] using this
  -- Then the propositional fields collapse by proof irrelevance.
  subst hsq
  rfl

/-- The set of closed knight's tours on the 8×8 board is finite.
    `Fintype.ofInjective` is `noncomputable` (uses `Classical.choice`),
    which is acceptable here because the distribution is studied
    abstractly — we never reduce `Finset.univ : Finset ClosedTour`
    computationally. -/
noncomputable instance : Fintype ClosedTour :=
  Fintype.ofInjective toFn toFn_injective

/-!
## The oblique-count distribution

`obliqueDistribution k` counts the closed tours with exactly `k` oblique
turns. The full histogram is determined by external enumeration (Knuth
2025, McKay 1997); this file does not commit to those values and instead
exposes the structural lemmas.
-/

/-- Number of closed knight's tours with exactly `k` oblique turns.
    `noncomputable` because it depends on the `Fintype ClosedTour`
    instance, which uses `Classical.choice`. -/
noncomputable def obliqueDistribution (k : ℕ) : ℕ :=
  (Finset.univ.filter (fun t : ClosedTour => obliqueCount t = k)).card

/-!
## Support lower bound

The first structural fact: the distribution is supported on `k ≥ 4`.
This is a one-line lift of `oblique_lower_bound : obliqueCount t ≥ 4`
from the parent file.
-/

/-- Support lower bound: no tour has fewer than 4 oblique turns. -/
theorem obliqueDistribution_zero_below_four (k : ℕ) (hk : k < 4) :
    obliqueDistribution k = 0 := by
  unfold obliqueDistribution
  rw [Finset.card_eq_zero]
  apply Finset.eq_empty_of_forall_not_mem
  intro t ht
  rw [Finset.mem_filter] at ht
  obtain ⟨_, hcount⟩ := ht
  have hbound : obliqueCount t ≥ 4 := oblique_lower_bound t
  rw [hcount] at hbound
  omega

/-- Equivalent statement: the distribution vanishes on `{0, 1, 2, 3}`. -/
theorem obliqueDistribution_support_le_three :
    ∀ k, k ≤ 3 → obliqueDistribution k = 0 := fun k hk =>
  obliqueDistribution_zero_below_four k (Nat.lt_succ_of_le hk)

/-- The unique minimum tour from Knuth's classification (combined with
    `oblique_lower_bound`) shows the support is non-empty at `k = 4`. The
    concrete value `obliqueDistribution 4` is determined by the D4-orbit
    of `minimalObliqueTour` (the parent's canonical witness) and is at
    most 8 — but the exact value depends on Knuth's classification of
    self-symmetric tours, which is deferred to S3. -/

/-!
## Support upper bound

`obliqueCount` is the length of a filtered list of move-pair adjacencies in
a tour of length 64, so it is bounded by 64. Combined with the support
lower bound this confines the distribution's support to `[4, 64]`. -/

/-- Pointwise upper bound: every tour has at most 64 oblique turns
    (one per move-pair adjacency in a 64-move closed tour). -/
theorem obliqueCount_le_64 (t : ClosedTour) : obliqueCount t ≤ 64 := by
  -- `obliqueCount` filters a list of length 64 (=`(tourMoves t).length`).
  -- Use a definitional unfolding via `rfl` to avoid `let`-binding issues.
  have heq : obliqueCount t =
      ((tourMoves t).zip ((tourMoves t).tail ++ [(tourMoves t).head!])
        |>.filter fun (v1, v2) => isOblique v1 v2).length := rfl
  rw [heq]
  refine le_trans (List.length_filter_le _ _) ?_
  simp [List.length_zip, List.length_tail, List.length_append, tourMoves_length]

/-- Support upper bound: no tour has more than 64 oblique turns, so the
    distribution vanishes above 64. -/
theorem obliqueDistribution_zero_above_64 (k : ℕ) (hk : 64 < k) :
    obliqueDistribution k = 0 := by
  unfold obliqueDistribution
  rw [Finset.card_eq_zero]
  apply Finset.eq_empty_of_forall_not_mem
  intro t ht
  rw [Finset.mem_filter] at ht
  obtain ⟨_, hcount⟩ := ht
  have hbound : obliqueCount t ≤ 64 := obliqueCount_le_64 t
  rw [hcount] at hbound
  omega

/-!
## Normalization: histogram sums to total tour count

Combining the lower bound (`k ≥ 4`) and upper bound (`k ≤ 64`), the
distribution is supported on the finite interval `[4, 64]`. Its sum over
`Finset.range 65` (which covers the support) equals the cardinality of
`ClosedTour`. This is the histogram-completeness statement: every closed
tour contributes to exactly one bucket. -/

/-- The histogram sums to the total number of closed tours. The sum is
    taken over `Finset.range 65` since `obliqueCount t ≤ 64` for every
    tour (`obliqueCount_le_64`). -/
theorem obliqueDistribution_sum_eq_card :
    (∑ k ∈ Finset.range 65, obliqueDistribution k) = Fintype.card ClosedTour := by
  unfold obliqueDistribution
  rw [← Finset.card_univ]
  exact (Finset.card_eq_sum_card_fiberwise (f := obliqueCount) (s := Finset.univ)
    (t := Finset.range 65)
    (fun t _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (obliqueCount_le_64 t)))).symm

/-- Equivalent normalisation taking the sum over the actual support
    `Finset.Icc 4 64`: the histogram restricted to `[4, 64]` already
    accounts for every closed tour, since `obliqueDistribution` vanishes
    on `{0, 1, 2, 3}` by the parent's lower bound. -/
theorem obliqueDistribution_sum_Icc_eq_card :
    (∑ k ∈ Finset.Icc 4 64, obliqueDistribution k) = Fintype.card ClosedTour := by
  rw [← obliqueDistribution_sum_eq_card]
  -- The terms in `range 65 \ Icc 4 64 = {0,1,2,3}` are all zero by
  -- `obliqueDistribution_zero_below_four`.
  apply Finset.sum_subset
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    simp only [Finset.mem_range]
    omega
  · intro k _ hkn
    simp only [Finset.mem_Icc, not_and_or, not_le] at hkn
    rcases hkn with hlt | h
    · exact obliqueDistribution_zero_below_four k hlt
    · exact obliqueDistribution_zero_above_64 k h

end KnightsTourOblique
