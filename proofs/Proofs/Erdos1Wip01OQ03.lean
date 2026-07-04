/-
  Erdős Problem #1 — WIP Extension, OQ03: The Conway–Guy Construction

  Erdős #1 asks for the minimum possible largest element `f(n)` of a set of `n`
  positive integers all of whose subset sums are distinct (a "Sidon-for-sums"
  or *distinct-subset-sums* (DSS) set).

  The trivial construction `{1, 2, 4, …, 2^(n-1)}` (formalized in
  `Erdos1Wip01.lean` as `powers_of_two_has_dss`) shows `f(n) ≤ 2^(n-1)`.
  Conway and Guy (1968) discovered a family that does **strictly better**: for
  every `n ≥ 4` there is a DSS set of size `n` whose largest element is
  *strictly below* `2^(n-1)`. Their sets are the difference sets of the
  Conway–Guy sequence `a = 0, 1, 2, 4, 7, 13, 24, 44, 84, 161, …`
  (OEIS A005318): the `n`-element set is `{a(n) − a(n−i) : 1 ≤ i ≤ n}`.

  **What this file contributes.**

  1. `hasDistinctSubsetSums_iff_image_card` — a *decidable* reformulation of the
     DSS property: `A` has distinct subset sums iff the number of *distinct*
     subset sums equals the number of subsets `2^|A|`. The bare definition
     quantifies over all of `Finset ℕ`, so it is not decidable as written; this
     lemma reduces it to an injectivity check on `A.powerset`, which `decide`
     can settle for concrete `A`. This is reusable infrastructure for the whole
     Erdős #1 family.

  2. Explicit Conway–Guy witnesses `cg4 … cg8`, each verified by kernel
     `decide` (no `native_decide`, hence no `Lean.ofReduceBool`): every one has
     distinct subset sums, has the right cardinality, and has largest element
     strictly below the powers-of-two bound `2^(n-1)`.

  3. `conwayGuy_beats_powers_of_two` — the packaged statement that for each
     `n ∈ {4,5,6,7,8}` there is an `n`-element DSS set with largest element
     `< 2^(n-1)`, so the powers-of-two construction is *not* optimal.

  **What remains open (the OQ).** Whether the Conway–Guy sets are *optimal*
  (achieve `f(n)`) is known only for `n ≤ 10` (verified computationally) and is
  open for `n ≥ 11`. Proving optimality — or even the `< 2^(n-1)` gap — for
  *all* `n` requires the general recurrence `a(n+1) = 2a(n) − a(n−r)`,
  `r = round(√(2n))`, whose subset-sum-distinctness has no known elementary
  induction. This file certifies the phenomenon on explicit cases; the general
  bound stays open.

  References:
  - Conway, Guy (1968): Solution of a problem of Erdős (the construction here)
  - Erdős (1955): Problems in additive number theory
  - Guy, Unsolved Problems in Number Theory, C8
  - OEIS A005318
-/

import Proofs.Erdos1Problem
import Mathlib

open Finset

-- The `decide` calls certifying distinct subset sums for the larger Conway–Guy
-- witnesses (n = 7, 8) evaluate a powerset-image cardinality over 2ⁿ subsets,
-- which exceeds the default elaboration recursion depth.
set_option maxRecDepth 10000

namespace Erdos1WIPOQ03

/-! ═══════════════════════════════════════════════════════════════════════════
PART I: A DECIDABLE CRITERION FOR DISTINCT SUBSET SUMS

`hasDistinctSubsetSums A` is defined by a universal quantifier over *all*
`Finset ℕ`, which is not decidable. We reduce it to injectivity of the
subset-sum map on the (finite) powerset, which `decide` can evaluate.
═══════════════════════════════════════════════════════════════════════════ -/

/-- **Decidable criterion for distinct subset sums.** `A` has distinct subset
    sums iff the map `S ↦ ∑ S` is injective on `A.powerset`, equivalently iff
    the number of *distinct* subset sums equals the number `2^|A|` of subsets.

    The right-hand side is a `Finset` cardinality identity, hence decidable, so
    concrete instances follow by `decide`. -/
theorem hasDistinctSubsetSums_iff_image_card (A : Finset ℕ) :
    hasDistinctSubsetSums A ↔
      (A.powerset.image (fun S => S.sum id)).card = A.powerset.card := by
  rw [Finset.card_image_iff]
  constructor
  · -- DSS ⇒ injective-on-powerset
    intro h a ha b hb hab
    exact h a b (Finset.mem_powerset.mp (Finset.mem_coe.mp ha))
      (Finset.mem_powerset.mp (Finset.mem_coe.mp hb)) hab
  · -- injective-on-powerset ⇒ DSS
    intro h S T hS hT hST
    exact h (Finset.mem_coe.mpr (Finset.mem_powerset.mpr hS))
      (Finset.mem_coe.mpr (Finset.mem_powerset.mpr hT)) hST

/-- Convenience form with the explicit `2^|A|` count of subsets. -/
theorem hasDistinctSubsetSums_iff_card_pow (A : Finset ℕ) :
    hasDistinctSubsetSums A ↔
      (A.powerset.image (fun S => S.sum id)).card = 2 ^ A.card := by
  rw [hasDistinctSubsetSums_iff_image_card, Finset.card_powerset]

/-! ═══════════════════════════════════════════════════════════════════════════
PART II: EXPLICIT CONWAY–GUY WITNESSES

Each `cgN` is the `N`-element difference set of the Conway–Guy sequence
`0,1,2,4,7,13,24,44,84,…`. We certify by kernel `decide` that each has distinct
subset sums, the correct cardinality, and largest element strictly below the
powers-of-two bound `2^(N-1)`.
═══════════════════════════════════════════════════════════════════════════ -/

/-- Conway–Guy set of size 4: `{3,5,6,7}`, largest element `7 < 8 = 2^3`. -/
def cg4 : Finset ℕ := {3, 5, 6, 7}
/-- Conway–Guy set of size 5: `{6,9,11,12,13}`, largest element `13 < 16 = 2^4`. -/
def cg5 : Finset ℕ := {6, 9, 11, 12, 13}
/-- Conway–Guy set of size 6: `{11,17,20,22,23,24}`, largest element `24 < 32 = 2^5`. -/
def cg6 : Finset ℕ := {11, 17, 20, 22, 23, 24}
/-- Conway–Guy set of size 7: `{20,31,37,40,42,43,44}`, largest element `44 < 64 = 2^6`. -/
def cg7 : Finset ℕ := {20, 31, 37, 40, 42, 43, 44}
/-- Conway–Guy set of size 8: `{40,60,71,77,80,82,83,84}`, largest element `84 < 128 = 2^7`. -/
def cg8 : Finset ℕ := {40, 60, 71, 77, 80, 82, 83, 84}

-- Cardinalities.
theorem cg4_card : cg4.card = 4 := by decide
theorem cg5_card : cg5.card = 5 := by decide
theorem cg6_card : cg6.card = 6 := by decide
theorem cg7_card : cg7.card = 7 := by decide
theorem cg8_card : cg8.card = 8 := by decide

-- Distinct subset sums (via the decidable criterion).
theorem cg4_dss : hasDistinctSubsetSums cg4 := by
  rw [hasDistinctSubsetSums_iff_image_card]; decide
theorem cg5_dss : hasDistinctSubsetSums cg5 := by
  rw [hasDistinctSubsetSums_iff_image_card]; decide
theorem cg6_dss : hasDistinctSubsetSums cg6 := by
  rw [hasDistinctSubsetSums_iff_image_card]; decide
theorem cg7_dss : hasDistinctSubsetSums cg7 := by
  rw [hasDistinctSubsetSums_iff_image_card]; decide
theorem cg8_dss : hasDistinctSubsetSums cg8 := by
  rw [hasDistinctSubsetSums_iff_image_card]; decide

-- Every element is below the powers-of-two bound `2^(n-1)`.
theorem cg4_lt : ∀ x ∈ cg4, x < 2 ^ 3 := by decide
theorem cg5_lt : ∀ x ∈ cg5, x < 2 ^ 4 := by decide
theorem cg6_lt : ∀ x ∈ cg6, x < 2 ^ 5 := by decide
theorem cg7_lt : ∀ x ∈ cg7, x < 2 ^ 6 := by decide
theorem cg8_lt : ∀ x ∈ cg8, x < 2 ^ 7 := by decide

/-! ═══════════════════════════════════════════════════════════════════════════
PART III: THE POWERS-OF-TWO CONSTRUCTION IS NOT OPTIMAL

For each `n ∈ {4,…,8}` there is an `n`-element DSS set all of whose elements are
`< 2^(n-1)`. Since the powers-of-two set `{1,…,2^(n-1)}` attains the value
`2^(n-1)`, the Conway–Guy set strictly improves on it.
═══════════════════════════════════════════════════════════════════════════ -/

/-- **Conway–Guy beats powers of two.** For every `n ∈ {4,5,6,7,8}` there exists
    a set `A` of `n` positive integers with distinct subset sums whose every
    element is strictly below `2^(n-1)` — the value attained by the
    powers-of-two construction. Hence powers-of-two is not optimal for these `n`. -/
theorem conwayGuy_beats_powers_of_two :
    ∀ n ∈ ({4, 5, 6, 7, 8} : Finset ℕ),
      ∃ A : Finset ℕ, A.card = n ∧ hasDistinctSubsetSums A ∧
        (∀ x ∈ A, 0 < x) ∧ (∀ x ∈ A, x < 2 ^ (n - 1)) := by
  intro n hn
  fin_cases hn
  · exact ⟨cg4, cg4_card, cg4_dss, by decide, cg4_lt⟩
  · exact ⟨cg5, cg5_card, cg5_dss, by decide, cg5_lt⟩
  · exact ⟨cg6, cg6_card, cg6_dss, by decide, cg6_lt⟩
  · exact ⟨cg7, cg7_card, cg7_dss, by decide, cg7_lt⟩
  · exact ⟨cg8, cg8_card, cg8_dss, by decide, cg8_lt⟩

end Erdos1WIPOQ03
