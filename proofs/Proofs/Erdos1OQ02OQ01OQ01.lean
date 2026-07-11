import Proofs.Erdos1OQ02OQ01

/-!
# Erdős #1, grandchild OQ-02-OQ-01-OQ-01: the doubling wall `2^{n-1}` is not tight

The parent `erdos-1-oq-02-oq-01` pins the Erdős extremal maximum

> `M(n) := min { max A : |A| = n, A has distinct subset sums }`

between the two elementary walls `(2ⁿ − 1)/n ≤ M(n) ≤ 2^{n-1}`, the upper wall
coming from the powers-of-two set `{2⁰, …, 2^{n-1}}` (parent Section 4). Because
the powers of two give `max A = 2^{n-1} = 2ⁿ/2`, that construction only shows the
conjectural constant `c` in Erdős's `max A ≥ c·2^{|A|}` satisfies `c ≤ 1/2`.

This entry records the first concrete evidence that the upper wall `2^{n-1}` is
**not tight**, i.e. that `c` can be pushed strictly below `1/2`. Conway and Guy
observed that

> `A = {3, 5, 6, 7}`

is a distinct-subset-sums set of cardinality `4` whose largest element is only
`7 < 8 = 2^{4-1}`. Its `2⁴ = 16` subset sums

> `0, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 21`

are pairwise distinct, so `M(4) ≤ 7 < 2^{4-1}`. For `n ≤ 3` the powers of two are
optimal (`M(1)=1, M(2)=2, M(3)=4 = 2^{n-1}`); `n = 4` is the *smallest* case where
the doubling construction is beaten. Note `{3,5,6,7}` is **not** superincreasing
(the elements below `7` sum to `3 + 5 + 6 = 14 ≥ 7`), so — unlike the powers of
two — its distinctness does not follow from the parent's
`Superincreasing.hasDistinctSubsetSums` engine; it is a genuinely different,
non-greedy construction. The full Conway–Guy sequence pushes the upper wall down to
`max A < 0.35·2ⁿ` asymptotically (and Bohman further to `< 0.22·2ⁿ`), but even this
single instance already certifies `c < 1/2`.

Distinctness is checked by the finite-verification lemma
`hasDistinctSubsetSums_iff_card_image`: a finite set `A` has distinct subset sums
**iff** its `2^{|A|}` subset sums are genuinely distinct, i.e.
`(A.powerset.image (·.sum id)).card = 2^{|A|}`. For a concrete `A` this reduces the
`∀ S T` definition to a single `decide`-able cardinality computation.

All results are `0`-axiom (no `sorry`, no `axiom`, no `native_decide`).

## References
* J. H. Conway and R. K. Guy, *Sets of natural numbers with distinct subset sums*,
  Notices Amer. Math. Soc. **15** (1968), 345.
* R. K. Guy, *Sets of integers whose subsets have distinct sums*, in
  Ann. Discrete Math. **12** (1982), 141–154.
* T. Bohman, *A sum packing problem of Erdős and the Conway–Guy sequence*,
  Proc. Amer. Math. Soc. **124** (1996), 3627–3636.
-/

namespace Erdos1OQ02OQ01

open Finset

/-!
## A decidable characterization of distinct subset sums

The definition `HasDistinctSubsetSums` quantifies over *all* finsets `S T : Finset ℕ`
with `S, T ⊆ A`, which is not directly `decide`-able. The following equivalence
replaces it by a single cardinality equation over the (finite) powerset of `A`,
which *is* decidable for a concrete `A`.
-/

/-- **Finite characterization.** `A` has distinct subset sums iff the subset-sum map
    is injective on its powerset, i.e. the `2^{|A|}` subset sums are pairwise
    distinct: `(A.powerset.image (·.sum id)).card = 2^{|A|}`. The forward direction
    is `subsetSum_injOn`; the reverse uses `Finset.injOn_of_card_image_eq`. -/
theorem hasDistinctSubsetSums_iff_card_image {A : Finset ℕ} :
    HasDistinctSubsetSums A ↔
      (A.powerset.image (fun S => S.sum id)).card = 2 ^ A.card := by
  constructor
  · intro h
    rw [card_image_of_injOn (subsetSum_injOn h), card_powerset]
  · intro h
    have hcard : (A.powerset.image (fun S => S.sum id)).card = A.powerset.card := by
      rw [h, card_powerset]
    have hinj := Finset.injOn_of_card_image_eq hcard
    intro S T hS hT hST
    exact hinj (Finset.mem_coe.mpr (mem_powerset.mpr hS))
      (Finset.mem_coe.mpr (mem_powerset.mpr hT)) hST

/-!
## Section 6: the Conway–Guy witness `{3, 5, 6, 7}`
-/

/-- The Conway–Guy 4-element witness `{3, 5, 6, 7}`: a distinct-subset-sums set whose
    maximum `7` beats the powers-of-two upper wall `2^{4-1} = 8`. -/
def conwayGuy4 : Finset ℕ := {3, 5, 6, 7}

/-- `{3, 5, 6, 7}` has exactly `4` elements. -/
theorem conwayGuy4_card : conwayGuy4.card = 4 := by decide

/-- **The Conway–Guy set has distinct subset sums.** Its `16` subset sums
    `0,3,5,6,7,8,9,10,11,12,13,14,15,16,18,21` are pairwise distinct, checked via
    the finite characterization `hasDistinctSubsetSums_iff_card_image`. -/
theorem conwayGuy4_hasDistinctSubsetSums : HasDistinctSubsetSums conwayGuy4 := by
  rw [hasDistinctSubsetSums_iff_card_image]
  decide

/-- The Conway–Guy set is **not** superincreasing: the elements strictly below `7`
    are `{3, 5, 6}` and sum to `14 ≥ 7`, so the superincreasing condition
    `(A.filter (· < 7)).sum id < 7` fails at `a = 7`. This is why its distinctness
    cannot come from the parent's `Superincreasing.hasDistinctSubsetSums` engine — it
    is a genuinely non-greedy construction, unlike the powers of two. -/
theorem conwayGuy4_not_superincreasing : ¬ Superincreasing conwayGuy4 := by
  intro h
  have := h 7 (by decide)
  revert this
  decide

/-- The largest element of the Conway–Guy set is `7`, strictly below the
    powers-of-two upper wall `2^{4-1} = 8`. -/
theorem conwayGuy4_max_lt (hne : conwayGuy4.Nonempty) :
    conwayGuy4.max' hne < 2 ^ (4 - 1) := by
  rw [Finset.max'_lt_iff]
  decide

/-- **The doubling wall `2^{n-1}` is not tight.** There is a distinct-subset-sums set
    of cardinality `4` whose maximum is strictly less than `2^{4-1} = 8`, namely
    `{3, 5, 6, 7}` with maximum `7`. Hence the Erdős extremal maximum satisfies
    `M(4) ≤ 7 < 2^{4-1}`: the powers-of-two upper wall of the parent entry is *not*
    attained, so the conjectural constant `c` in `max A ≥ c·2^{|A|}` is strictly
    below `1/2`. This is the smallest case where the doubling construction is beaten
    (`M(n) = 2^{n-1}` for `n ≤ 3`). -/
theorem exists_beat_doubling_wall :
    ∃ A : Finset ℕ, A.card = 4 ∧ HasDistinctSubsetSums A ∧
      ∃ hne : A.Nonempty, A.max' hne < 2 ^ (4 - 1) := by
  have hne : conwayGuy4.Nonempty := ⟨3, by decide⟩
  exact ⟨conwayGuy4, conwayGuy4_card, conwayGuy4_hasDistinctSubsetSums,
    hne, conwayGuy4_max_lt hne⟩

/-- Packaged comparison with the parent's powers-of-two construction at `n = 4`:
    both `{3,5,6,7}` (max `7`) and `geomSet 4 = {1,2,4,8}` (max `8`) are
    distinct-subset-sums 4-sets, and the Conway–Guy maximum is strictly smaller —
    an explicit witness that the parent's upper wall `max = 2^{n-1}` is beatable. -/
theorem conwayGuy4_beats_geomSet4 :
    ∃ (hCG : conwayGuy4.Nonempty) (hG : (geomSet 4).Nonempty),
      HasDistinctSubsetSums conwayGuy4 ∧ HasDistinctSubsetSums (geomSet 4) ∧
      conwayGuy4.max' hCG < (geomSet 4).max' hG := by
  have hCG : conwayGuy4.Nonempty := ⟨3, by decide⟩
  have hG : (geomSet 4).Nonempty := by
    rw [← card_pos, card_geomSet]; omega
  refine ⟨hCG, hG, conwayGuy4_hasDistinctSubsetSums, geomSet_hasDistinctSubsetSums 4, ?_⟩
  have h1 : conwayGuy4.max' hCG < 2 ^ (4 - 1) := conwayGuy4_max_lt hCG
  have h2 : (geomSet 4).max' hG = 2 ^ (4 - 1) := max'_geomSet (by omega) hG
  omega

end Erdos1OQ02OQ01
