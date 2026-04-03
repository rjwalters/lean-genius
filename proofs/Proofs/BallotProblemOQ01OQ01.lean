/-
# Completing the Dvoretzky-Motzkin Cycle Lemma

## Open Question: ballot-problem-oq-01-oq-01

This file completes the cycle lemma lower bound infrastructure for BallotProblemOQ01.lean.

**`ballot_discrete_ivt`** (the discrete IVT): For a {+1, -k}-list, if
- Some position achieves prefix sum = v (a lower witness)
- The final sum exceeds v

then some position j < l.length also achieves prefix sum = v.

**`rightmost_is_good_rotation`**: The rightmost position achieving level v,
where minPS ≤ v < minPS + S, is a good rotation. This is the key structural
step connecting the IVT to the cycle lemma lower bound.

**`cycle_lemma_lower_bound_via_ivt`**: Using the IVT and rightmostness, there are
at least a - k*b good rotations for any kCountedSequence with a > k*b.

## Proof Strategy (Finset.max' approach)

For the IVT, let S = {positions with prefix sum ≤ v}. S is nonempty (contains witness i₀).
Let j = max of S. Then:
- P(j) ≤ v (since j ∈ S)
- P(j+1) > v (since j+1 ∉ S, by maximality)
- The step l[j] must be +1 (not -k, since -k gives P(j+1) ≤ v)
- Therefore P(j) = v (since P(j) + 1 = P(j+1) > v and P(j) ≤ v)

For the rightmost position i at level v (minPS ≤ v < minPS+S):
- Non-wrapping (i+j ≤ l.length): cyclicP(j) = P(i+j) - P(i) > 0 by rightmostness
- Wrapping (i+j > l.length): cyclicP(j) = P(r) + S - v ≥ minPS + S - v > 0

## Status

- [x] `ballot_discrete_ivt` — PROVED (standalone, minimal imports)
- [x] `rightmost_is_good_rotation` — PROVED (via GeneralizedBallot.rightmostAtLevel_good)
- [x] `cycle_lemma_lower_bound_via_ivt` — PROVED (via GeneralizedBallot.goodRotations_card_ge)

## References

- BallotProblemOQ01.lean — full cycle lemma proof with infrastructure
- Dvoretzky & Motzkin (1947) — original cycle lemma paper
-/

import Proofs.BallotProblemOQ01
import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic

open GeneralizedBallot

/-- **Discrete IVT for ballot-type sequences**:

If a {+1, -k}-list has some position achieving prefix sum v,
and the final list sum exceeds v, then there's a position j < l.length
with prefix sum exactly v.

This is the foundational lemma for the Cycle Lemma lower bound:
it ensures that every level v ∈ [minPrefixSum, sum) is achieved,
giving at least (sum) many distinct good rotations. -/
theorem ballot_discrete_ivt {k : ℕ} (l : List ℤ)
    (hmem : ∀ x ∈ l, x = 1 ∨ x = -(k : ℤ))
    (v : ℤ)
    (hv_achieved : ∃ i₀, i₀ ≤ l.length ∧ (l.take i₀).sum = v)
    (hv_exceeded : v < l.sum) :
    ∃ j, j < l.length ∧ (l.take j).sum = v := by
  obtain ⟨i₀, hi₀_le, hi₀_eq⟩ := hv_achieved
  -- Finset S of positions in [0, l.length] with prefix sum ≤ v
  let S := (Finset.range (l.length + 1)).filter (fun i => (l.take i).sum ≤ v)
  -- S is nonempty: i₀ ∈ S
  have hS_ne : S.Nonempty :=
    ⟨i₀, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by rw [hi₀_eq]⟩⟩
  -- Let j = max of S (rightmost position with prefix sum ≤ v)
  obtain ⟨j, hj_max⟩ : ∃ j, j = S.max' hS_ne := ⟨S.max' hS_ne, rfl⟩
  have hj_mem : j ∈ S := hj_max ▸ Finset.max'_mem S hS_ne
  -- j is in [0, l.length] with P(j) ≤ v
  have hj_bound : j ≤ l.length :=
    Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hj_mem).1)
  have hj_le_v : (l.take j).sum ≤ v := (Finset.mem_filter.mp hj_mem).2
  -- j < l.length (since P(l.length) = l.sum > v)
  have hj_lt : j < l.length := by
    rcases Nat.eq_or_lt_of_le hj_bound with rfl | hlt
    · rw [List.take_length] at hj_le_v; linarith
    · exact hlt
  -- j+1 ∉ S: P(j+1) > v (by maximality of j)
  have hj1_gt : v < (l.take (j + 1)).sum := by
    by_contra hle; push_neg at hle
    have hj1_in : j + 1 ∈ S := Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by omega), hle⟩
    have := Finset.le_max' S (j + 1) (hj_max ▸ hj1_in)
    omega
  -- The element l[j] must be +1 (not -k)
  have hj_elem : l[j] = (1 : ℤ) := by
    -- l[j] ∈ l, so l[j] = 1 or l[j] = -k
    rcases hmem l[j] (List.getElem_mem hj_lt) with h1 | hk
    · exact h1
    · -- If l[j] = -k, then P(j+1) = P(j) - k ≤ v - k < v, contradicts hj1_gt
      rw [List.sum_take_succ l j hj_lt, hk] at hj1_gt; linarith
  -- Therefore P(j) = v
  have hj_eq : (l.take j).sum = v := by
    rw [List.sum_take_succ l j hj_lt, hj_elem] at hj1_gt; linarith
  exact ⟨j, hj_lt, hj_eq⟩

/-- **Rightmost position at level v is a good rotation**.

    For a list l with sum S > 0, if position i satisfies:
    - P(i) = v (achieves level v)
    - minPrefixSum l ≤ v < minPrefixSum l + S  (v is in the valid range)
    - i is rightmost: ∀ j > i, j ≤ l.length → P(j) > v

    then i is a good rotation (all cyclic prefix sums > 0).

    **Proof** (see BallotProblemOQ01.rightmostAtLevel_good):
    For each offset j ∈ [1, l.length] in the cyclic rotation at i:
    - Non-wrapping (i+j ≤ l.length):
        cyclicPrefixSum(j) = P(i+j) - P(i) = P(i+j) - v > 0
        because i is rightmost at level v, so P(i+j) > v.
    - Wrapping (i+j > l.length):
        cyclicPrefixSum(j) = P(i+j-n) + S - P(i) = P(r) + S - v
        where r = i+j-n ∈ [0, l.length], so P(r) ≥ minPrefixSum l.
        Since v < minPrefixSum l + S, we get cyclicPrefixSum(j) > 0. -/
theorem rightmost_is_good_rotation (l : List ℤ)
    (hS : 0 < l.sum)
    (v : ℤ)
    (hlo : minPrefixSum l ≤ v) (hhi : v < minPrefixSum l + l.sum)
    (i : ℕ) (hi_lt : i < l.length)
    (hi_eq : (l.take i).sum = v)
    (hi_right : ∀ j, i < j → j ≤ l.length → v < (l.take j).sum) :
    isGoodRotation l i :=
  rightmostAtLevel_good l v hS hlo hhi i hi_lt
    (show prefixSum l i = v from hi_eq)
    (fun j hj hjn => hi_right j hj hjn)

/-- **Cycle Lemma lower bound via the IVT**:

    For a kCountedSequence l with a > k*b, there are at least a - k*b good rotations.

    **Proof sketch using the IVT** (formalized in BallotProblemOQ01.lean):
    1. For each n ∈ {0, ..., a-kb-1}, level (minPS + n) lies in [minPS, minPS+S).
    2. By `ballot_discrete_ivt` (IVT), this level is achieved at some position.
    3. The rightmost such position is a good rotation (by `rightmost_is_good_rotation`).
    4. These a-kb positions are distinct (they achieve different prefix sum levels).

    Combined with the upper bound `goodRotations_card_le`, this gives the full cycle lemma:
    |goodRotations l| = a - k*b. -/
theorem cycle_lemma_lower_bound_via_ivt {k a b : ℕ} {l : List ℤ}
    (hl : l ∈ kCountedSequence k a b)
    (hab : k * b < a) :
    a - k * b ≤ (goodRotations l).card :=
  goodRotations_card_ge hl hab
