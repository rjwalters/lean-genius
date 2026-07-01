/-
  A quantitative lower bound on the counting function of ODD abundant numbers.

  `AbundantOddInfiniteOQ03.lean` shows the set of odd abundant numbers is
  infinite, via the witness family `945·(2k+1) = 945, 2835, 4725, …` (each a
  positive odd multiple of the smallest odd abundant seed `945 = 3³·5·7`).
  Infinitude is a purely qualitative statement. This file sharpens it to an
  explicit *counting* bound, the first of the open questions raised by that
  entry:

      #{ n ≤ N : n odd and abundant }  ≥  N / 1890.

  Equivalently, odd abundant numbers have **positive lower density**
  ≥ 1/1890 among all positive integers — a quantitative strengthening of
  infinitude. The constant comes directly from the witness spacing: the
  members of `945·(2k+1)` below `N` number roughly `N/1890`, since consecutive
  witnesses differ by `2·945 = 1890`.

  The bound is not claimed to be sharp; the true density of odd abundant
  numbers is larger (the family `945·(2k+1)` misses every odd abundant number
  not divisible by `945`). What it *does* give is a clean, dimension-free,
  axiom-free linear lower bound, resting only on:
    * `odd_abundant_945_mul`  — every `945·(2k+1)` is odd and abundant,
    * `odd_mul_succ_injective` — the witnesses are pairwise distinct.

  The proof is axiom-free (no `sorry`, no `axiom`, no `native_decide`).
-/
import Mathlib
import Proofs.AbundantOddInfiniteOQ03

namespace AbundantOddDensityOQ0301

open AbundantOddInfiniteOQ03

-- Match the base files' classical decidability setup so `Finset.filter` may
-- range over the (decidable, but conveniently classical) predicate
-- `fun n => Odd n ∧ n.Abundant`.
attribute [local instance] Classical.propDecidable

/-- The counting function of odd abundant numbers: the number of `n` with
`1 ≤ n ≤ N` that are both odd and abundant. -/
noncomputable def oddAbundantCount (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter (fun n => Odd n ∧ n.Abundant)).card

/-- **Core counting estimate.** If `1890·m ≤ N`, then there are at least `m`
odd abundant numbers in `[1, N]`.

The first `m` witnesses `945·(2k+1)` (`k = 0, …, m-1`) are pairwise distinct
odd abundant numbers, and the largest of them, `945·(2m-1) ≤ 1890·m ≤ N`,
still lies in `[1, N]`. Hence the filtered set contains an injective image of
`range m`, so its cardinality is at least `m`. -/
theorem count_lower_bound (N m : ℕ) (h : 1890 * m ≤ N) :
    m ≤ oddAbundantCount N := by
  unfold oddAbundantCount
  -- The image of `range m` under `k ↦ 945·(2k+1)` lands in the filtered set.
  have himg : (Finset.range m).image (fun k => 945 * (2 * k + 1)) ⊆
      (Finset.Icc 1 N).filter (fun n => Odd n ∧ n.Abundant) := by
    intro n hn
    simp only [Finset.mem_image, Finset.mem_range] at hn
    obtain ⟨k, hk, rfl⟩ := hn
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨Nat.one_le_iff_ne_zero.mpr (by positivity), ?_⟩, odd_abundant_945_mul k⟩
    -- `945·(2k+1) ≤ 945·(2m) = 1890·m ≤ N` since `k < m ⟹ 2k+1 ≤ 2m`.
    have hkm : 2 * k + 1 ≤ 2 * m := by omega
    calc 945 * (2 * k + 1) ≤ 945 * (2 * m) := Nat.mul_le_mul_left _ hkm
      _ = 1890 * m := by ring
      _ ≤ N := h
  -- The image has exactly `m` elements (the witness map is injective).
  have hcard : ((Finset.range m).image (fun k => 945 * (2 * k + 1))).card = m := by
    rw [Finset.card_image_of_injective _ odd_mul_succ_injective, Finset.card_range]
  calc m = ((Finset.range m).image (fun k => 945 * (2 * k + 1))).card := hcard.symm
    _ ≤ ((Finset.Icc 1 N).filter (fun n => Odd n ∧ n.Abundant)).card :=
        Finset.card_le_card himg

/-- **Explicit linear lower bound on the counting function.**

For every `N`, the number of odd abundant numbers in `[1, N]` is at least
`N / 1890` (natural-number division). In particular odd abundant numbers have
positive lower density ≥ 1/1890. -/
theorem oddAbundantCount_ge_div (N : ℕ) : N / 1890 ≤ oddAbundantCount N := by
  apply count_lower_bound
  -- `1890 · (N / 1890) ≤ N`.
  have := Nat.div_mul_le_self N 1890
  omega

/-- **Quantitative infinitude.** For every target `M`, there is a bound `N`
below which at least `M` odd abundant numbers occur — namely `N = 1890·M`.
This recovers `infinitely_many_odd_abundant` with an explicit rate. -/
theorem oddAbundantCount_unbounded (M : ℕ) : M ≤ oddAbundantCount (1890 * M) :=
  count_lower_bound (1890 * M) M (le_refl _)

/-- The counting function of odd abundant numbers tends to infinity: for every
`M` it is `≥ M` from `N = 1890·M` onward, so it is unbounded. -/
theorem oddAbundantCount_atTop (M : ℕ) : ∃ N, ∀ K, N ≤ K → M ≤ oddAbundantCount K :=
  ⟨1890 * M, fun K hK => count_lower_bound K M hK⟩

-- Confirms the result depends only on the standard foundational axioms
-- (propext, Classical.choice, Quot.sound) and NOT on `Lean.ofReduceBool`
-- (which `native_decide` would introduce) or `sorryAx`.
#print axioms oddAbundantCount_ge_div

end AbundantOddDensityOQ0301
