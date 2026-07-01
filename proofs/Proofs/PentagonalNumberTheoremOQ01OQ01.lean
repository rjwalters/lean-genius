/-
  # Pentagonal Number Theorem, OQ-01 → OQ-01:
    The ordered enumeration of the generalized pentagonal numbers (OEIS A001318)

  The parent entry `PentagonalNumberTheoremOQ01` builds the ℤ-indexed theory of the
  generalized pentagonal numbers `g(k) = k(3k-1)/2` — the recognition criterion
  (`m` is generalized pentagonal iff `24m+1` is a perfect square), injectivity of
  the index map `k ↦ g(k)`, nonnegativity, and the concrete values
  `g(0..±4) = 0,1,2,5,7,12,15,22,26`.  What it does **not** record is the *order*
  structure: the index map `g : ℤ → ℤ` is injective but neither monotone nor
  surjective onto an interval, and the generalized pentagonal numbers as a *set*
  carry a canonical strictly-increasing enumeration

      `0, 1, 2, 5, 7, 12, 15, 22, 26, 35, 40, …`   (OEIS A001318)

  obtained by interleaving the two arms `g(k)` (k ≥ 1) and `g(-k)` (k ≥ 1) around
  `g(0)=0`.  This file makes that enumeration precise.

  ## What is proved (all 0-sorry, 0-axiom, building only on the parent + Mathlib)

  * `genPent_succ_sub`            — the forward gap `g(k+1) - g(k) = 3k+1`;
  * `genPent_lt_genPent_neg`      — `g(k) < g(-k)` for `k ≥ 1`  (the `±k` pair is ordered);
  * `genPent_neg_lt_genPent_succ` — `g(-k) < g(k+1)` for `k ≥ 0`  (the interleaving step);
  * `gpAt : ℕ → ℤ`               — the enumeration `0 ↦ g 0`, `2j-1 ↦ g j`, `2j ↦ g (-j)`;
  * `gpAt_strictMono`            — **the enumeration is strictly increasing** (headline);
  * `gpAt_injective`             — hence injective;
  * `gpAt_isGenPent`             — every `gpAt n` is a generalized pentagonal number;
  * `gpRank` / `gpAt_gpRank`     — the inverse rank `g(k) = gpAt (gpRank k)`;
  * `isGenPent_iff_mem_range`    — **surjectivity**: `IsGenPent m ↔ ∃ n, gpAt n = m`;
  * `range_gpAt`                 — `Set.range gpAt = {m | IsGenPent m}` (range = the set);
  * `gpAt_enumerates`            — the capstone: `gpAt` is a strictly-increasing
                                   bijection onto the generalized pentagonal numbers;
  * `mem_range_gpAt_iff_isSquare`— ties the enumeration back to the parent's
                                   square-discriminant criterion.

  Together these say: the generalized pentagonal numbers are exactly the values of
  the strictly-monotone sequence `gpAt`, so `gpAt n` is *the n-th smallest*
  generalized pentagonal number — the order-theoretic content underlying A001318.
-/

import Mathlib
import Proofs.PentagonalNumberTheoremOQ01

set_option maxHeartbeats 400000

namespace PentagonalNumberTheoremOQ01OQ01

open PentagonalNumberTheoremOQ01

/-! ## Part 1: The forward gap and the ordering of the `±k` pair

The whole enumeration rests on three inequalities.  The forward gap
`g(k+1) - g(k) = 3k+1` is an exact algebraic identity (from `2g(k)=k(3k-1)`); the
parent's `genPent_neg : g(-k) = g(k)+k` then orders the `±k` pair and shows the
arms interleave. -/

/-- **Forward gap.** `g(k+1) - g(k) = 3k+1`, since `2(g(k+1)-g(k)) = (k+1)(3k+2) -
k(3k-1) = 6k+2`. -/
theorem genPent_succ_sub (k : ℤ) : genPent (k + 1) - genPent k = 3 * k + 1 := by
  have key : 2 * (genPent (k + 1) - genPent k) = 2 * (3 * k + 1) := by
    linear_combination two_mul_genPent (k + 1) - two_mul_genPent k
  linarith

/-- **The `±k` pair is ordered.** `g(k) < g(-k)` for `k ≥ 1`: by `genPent_neg`
their difference is exactly `k ≥ 1`. -/
theorem genPent_lt_genPent_neg {k : ℤ} (hk : 1 ≤ k) : genPent k < genPent (-k) := by
  rw [genPent_neg]; linarith

/-- **The arms interleave.** `g(-k) < g(k+1)` for `k ≥ 0`: from `genPent_neg`
(`g(-k)=g(k)+k`) and the gap (`g(k+1)=g(k)+3k+1`), the difference is `2k+1 ≥ 1`. -/
theorem genPent_neg_lt_genPent_succ {k : ℤ} (hk : 0 ≤ k) :
    genPent (-k) < genPent (k + 1) := by
  have hneg := genPent_neg k
  have hgap := genPent_succ_sub k
  linarith

/-! ## Part 2: The enumeration `gpAt`

`gpAt n` lists the generalized pentagonal numbers in increasing order: `gpAt 0 = g 0`,
the odd positions `2j-1` carry the positive arm `g j`, and the even positions `2j`
carry the negative arm `g(-j)`.  We package this with even/odd reduction lemmas so
the index bookkeeping (ℕ ↔ ℤ casts, `n % 2`, `n / 2`) is discharged once. -/

/-- The increasing enumeration of generalized pentagonal numbers.  Even index `2j`
gives the negative arm `g(-j)`; odd index `2j+1` gives the positive arm `g(j+1)`. -/
def gpAt (n : ℕ) : ℤ :=
  if n % 2 = 0 then genPent (-(n / 2 : ℕ)) else genPent ((n + 1) / 2 : ℕ)

/-- Reduction at even positions: `gpAt (2j) = g(-j)`. -/
theorem gpAt_even (j : ℕ) : gpAt (2 * j) = genPent (-(j : ℤ)) := by
  unfold gpAt
  rw [if_pos (by omega), show (2 * j) / 2 = j from by omega]

/-- Reduction at odd positions: `gpAt (2j+1) = g(j+1)`. -/
theorem gpAt_odd (j : ℕ) : gpAt (2 * j + 1) = genPent ((j : ℤ) + 1) := by
  unfold gpAt
  rw [if_neg (by omega), show (2 * j + 1 + 1) / 2 = j + 1 from by omega]
  norm_cast

/-- **Headline: the enumeration is strictly increasing.** Consecutive values satisfy
`gpAt n < gpAt (n+1)`: at an even step `2j → 2j+1` this is `g(-j) < g(j+1)`
(interleaving), at an odd step `2j+1 → 2j+2` it is `g(j+1) < g(-(j+1))` (ordered
pair). -/
theorem gpAt_strictMono : StrictMono gpAt := by
  apply strictMono_nat_of_lt_succ
  intro n
  rcases Nat.even_or_odd n with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · -- n = j + j (even)
    rw [show j + j = 2 * j from (two_mul j).symm, gpAt_even, gpAt_odd]
    exact genPent_neg_lt_genPent_succ (Nat.cast_nonneg j)
  · -- n = 2j + 1 (odd)
    rw [show 2 * j + 1 + 1 = 2 * (j + 1) from by ring, gpAt_odd, gpAt_even]
    have h1 : (1 : ℤ) ≤ (j : ℤ) + 1 := by have := Nat.cast_nonneg (α := ℤ) j; linarith
    have := genPent_lt_genPent_neg h1
    push_cast
    linarith

/-- The enumeration is injective (strict monotonicity). -/
theorem gpAt_injective : Function.Injective gpAt := gpAt_strictMono.injective

/-- Every enumerated value is a generalized pentagonal number. -/
theorem gpAt_isGenPent (n : ℕ) : IsGenPent (gpAt n) := by
  unfold gpAt
  split <;> exact genPent_isGenPent _

/-! ## Part 3: The inverse rank and surjectivity

`gpRank k` returns the position of `g(k)` in the enumeration, and `gpAt_gpRank`
shows it is a genuine inverse on values.  Combined with the fact that every
generalized pentagonal number is some `g(k)`, this gives surjectivity of `gpAt`
onto `{m | IsGenPent m}`. -/

/-- Every generalized pentagonal number is `g(k)` for an explicit index `k`. -/
theorem isGenPent_exists_index {m : ℤ} (h : IsGenPent m) : ∃ k : ℤ, m = genPent k := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k, ?_⟩
  have h2 : 2 * m = 2 * genPent k := by rw [hk, two_mul_genPent k]
  exact mul_left_cancel₀ (by norm_num) h2

/-- The rank of `g(k)` in the enumeration: positive indices land on odd positions,
nonpositive indices on even positions. -/
def gpRank (k : ℤ) : ℕ := if 1 ≤ k then 2 * (k.toNat - 1) + 1 else 2 * (-k).toNat

/-- **The rank inverts the enumeration on values:** `gpAt (gpRank k) = g(k)`. -/
theorem gpAt_gpRank (k : ℤ) : gpAt (gpRank k) = genPent k := by
  unfold gpRank
  by_cases hk : 1 ≤ k
  · rw [if_pos hk, gpAt_odd]
    congr 1
    have h0 : 0 ≤ k := by linarith
    have ht : (k.toNat : ℤ) = k := Int.toNat_of_nonneg h0
    have ht1 : 1 ≤ k.toNat := by omega
    rw [Nat.cast_sub ht1, ht]
    push_cast
    ring
  · rw [if_neg hk, gpAt_even]
    congr 1
    have h0 : 0 ≤ -k := by omega
    have ht : ((-k).toNat : ℤ) = -k := Int.toNat_of_nonneg h0
    rw [ht]
    ring

/-- **Surjectivity onto the generalized pentagonal numbers.** Every generalized
pentagonal number appears in the enumeration. -/
theorem exists_gpAt_eq {m : ℤ} (h : IsGenPent m) : ∃ n : ℕ, gpAt n = m := by
  obtain ⟨k, rfl⟩ := isGenPent_exists_index h
  exact ⟨gpRank k, gpAt_gpRank k⟩

/-- **Characterization of the range.** `m` is a generalized pentagonal number iff it
occurs in the enumeration `gpAt`. -/
theorem isGenPent_iff_mem_range (m : ℤ) : IsGenPent m ↔ ∃ n : ℕ, gpAt n = m :=
  ⟨exists_gpAt_eq, by rintro ⟨n, rfl⟩; exact gpAt_isGenPent n⟩

/-- **The range of the enumeration is exactly the set of generalized pentagonal
numbers.** -/
theorem range_gpAt : Set.range gpAt = {m : ℤ | IsGenPent m} := by
  ext m
  simp only [Set.mem_range, Set.mem_setOf_eq]
  exact (isGenPent_iff_mem_range m).symm

/-! ## Part 4: Capstone and the bridge to the square-discriminant criterion -/

/-- **Capstone.** The generalized pentagonal numbers are precisely the values of the
strictly-increasing sequence `gpAt`; equivalently, `gpAt n` is the `n`-th smallest
generalized pentagonal number.  This is the order-theoretic content underlying
OEIS A001318. -/
theorem gpAt_enumerates :
    StrictMono gpAt ∧ Set.range gpAt = {m : ℤ | IsGenPent m} :=
  ⟨gpAt_strictMono, range_gpAt⟩

/-- **Enumeration meets the recognition criterion.** Composing surjectivity with the
parent's square-discriminant criterion, a number occurs in the enumeration iff
`24m+1` is a perfect square. -/
theorem mem_range_gpAt_iff_isSquare (m : ℤ) :
    (∃ n : ℕ, gpAt n = m) ↔ ∃ s : ℤ, 24 * m + 1 = s ^ 2 := by
  rw [← isGenPent_iff_mem_range, isGenPent_iff_isSquare]

/-- Sanity check against OEIS A001318: the first seven terms are `0,1,2,5,7,12,15`. -/
theorem gpAt_values :
    gpAt 0 = 0 ∧ gpAt 1 = 1 ∧ gpAt 2 = 2 ∧ gpAt 3 = 5 ∧
      gpAt 4 = 7 ∧ gpAt 5 = 12 ∧ gpAt 6 = 15 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ## Part 5: The gap structure of the ordered enumeration (first differences of A001318)

`gpAt_strictMono` records only that the enumeration increases; it does not say *by how
much*.  The consecutive differences `gpAt (n+1) − gpAt n` of A001318 are
`1, 1, 3, 2, 5, 3, 7, 4, …` — two interleaved arithmetic progressions, one per parity of the
step.  An *even* step `2j → 2j+1` crosses from `g(−j)` up to `g(j+1)` and has gap `2j+1`
(the odd numbers `1, 3, 5, 7, …`); an *odd* step `2j+1 → 2j+2` crosses from `g(j+1)` to
`g(−(j+1))` and has gap `j+1` (the naturals `1, 2, 3, 4, …`).  Both follow from the parent's
`genPent_succ_sub` (`g(k+1) − g(k) = 3k+1`) and `genPent_neg` (`g(−k) = g(k) + k`).  Since
both gaps are `≥ 1`, this is a quantitative refinement of strict monotonicity. -/

/-- **Even-step gap (the odd progression).**  The step `gpAt (2j) → gpAt (2j+1)`, crossing
`g(−j) → g(j+1)`, increases by `2j+1`: `g(j+1) − g(−j) = (g(j+1) − g(j)) − j = (3j+1) − j`. -/
theorem gpAt_gap_odd (j : ℕ) :
    gpAt (2 * j + 1) - gpAt (2 * j) = 2 * (j : ℤ) + 1 := by
  rw [gpAt_odd, gpAt_even, genPent_neg]
  linarith [genPent_succ_sub (j : ℤ)]

/-- **Odd-step gap (the natural progression).**  The step `gpAt (2j+1) → gpAt (2j+2)`,
crossing `g(j+1) → g(−(j+1))`, increases by `j+1`: directly `g(−(j+1)) − g(j+1) = j+1`
by `genPent_neg`. -/
theorem gpAt_gap_even (j : ℕ) :
    gpAt (2 * j + 2) - gpAt (2 * j + 1) = (j : ℤ) + 1 := by
  rw [show 2 * j + 2 = 2 * (j + 1) from by ring, gpAt_even, gpAt_odd, genPent_neg]
  push_cast
  ring

/-- **Every gap is at least 1** — a quantitative form of strict monotonicity: each
consecutive difference of the enumeration is a positive integer (`≥ 1`), so the values
not only increase but never repeat and leave no room to "stall". -/
theorem gpAt_gap_pos (n : ℕ) : 1 ≤ gpAt (n + 1) - gpAt n := by
  rcases Nat.even_or_odd n with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · have h := gpAt_gap_odd j
    rw [show j + j = 2 * j from by ring]; omega
  · have h := gpAt_gap_even j
    rw [show 2 * j + 1 + 1 = 2 * j + 2 from by ring]; omega

/-- **The gap law (capstone).**  The first differences of the ordered enumeration A001318
are exactly the two interleaved progressions: even steps add the odd numbers `2j+1`, odd
steps add the naturals `j+1`. -/
theorem gpAt_gaps (j : ℕ) :
    gpAt (2 * j + 1) - gpAt (2 * j) = 2 * (j : ℤ) + 1
      ∧ gpAt (2 * j + 2) - gpAt (2 * j + 1) = (j : ℤ) + 1 :=
  ⟨gpAt_gap_odd j, gpAt_gap_even j⟩

/-- Sanity check of the gap law against A001318's first differences `1,1,3,2,5,3`. -/
theorem gpAt_gap_values :
    gpAt 1 - gpAt 0 = 1 ∧ gpAt 2 - gpAt 1 = 1 ∧ gpAt 3 - gpAt 2 = 3 ∧
      gpAt 4 - gpAt 3 = 2 ∧ gpAt 5 - gpAt 4 = 5 ∧ gpAt 6 - gpAt 5 = 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ## Part 6: The quadratic closed form and the growth/density of A001318

Parts 1–5 pin down the *order* of the enumeration (strict monotonicity, exact first
differences) but not its *rate of growth*.  Telescoping the two interleaved gap
progressions of Part 5 collapses to a single quadratic: `gpAt n` grows like `3n²/8`.
Precisely, `8·gpAt n = 3n²+2n` at even positions and `3n²+4n+1` at odd positions, so
the whole sequence is squeezed by

    `3n² ≤ 8·gpAt n ≤ 3n²+4n+1 ≤ 3(n+1)²`.

Two consequences:

* `gpAt n = Θ(n²)` — the `n`-th generalized pentagonal number is quadratic in `n`;
* **density / sparsity of A001318**: if `gpAt n ≤ N` then `3n² ≤ 8N`, i.e. `n ≤ √(8N/3)`,
  so at most `⌊√(8N/3)⌋+1` generalized pentagonal numbers lie in `[0, N]` — they thin
  out like `√N`, the reciprocal of the `Θ(n²)` growth. -/

/-- **Closed form at even positions.** `8·gpAt (2j) = 3(2j)² + 2(2j) = 12j²+4j`, from
`2·g(−j) = (−j)(−3j−1) = 3j²+j` (the parent's doubling relation at `−j`). -/
theorem gpAt_eight_even (j : ℕ) :
    8 * gpAt (2 * j) = 3 * (2 * (j : ℤ)) ^ 2 + 2 * (2 * (j : ℤ)) := by
  rw [gpAt_even]
  linear_combination (4 : ℤ) * two_mul_genPent (-(j : ℤ))

/-- **Closed form at odd positions.** `8·gpAt (2j+1) = 3(2j+1)² + 4(2j+1) + 1 =
12j²+20j+8`, from `2·g(j+1) = (j+1)(3j+2)`. -/
theorem gpAt_eight_odd (j : ℕ) :
    8 * gpAt (2 * j + 1) = 3 * (2 * (j : ℤ) + 1) ^ 2 + 4 * (2 * (j : ℤ) + 1) + 1 := by
  rw [gpAt_odd]
  linear_combination (4 : ℤ) * two_mul_genPent ((j : ℤ) + 1)

/-- **Lower growth bound.** `3n² ≤ 8·gpAt n` for every `n` — the `n`-th generalized
pentagonal number is at least `3n²/8`. -/
theorem gpAt_eight_lower (n : ℕ) : 3 * (n : ℤ) ^ 2 ≤ 8 * gpAt n := by
  rcases Nat.even_or_odd n with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [show j + j = 2 * j from (two_mul j).symm, gpAt_eight_even]
    push_cast; nlinarith [Nat.cast_nonneg (α := ℤ) j]
  · rw [gpAt_eight_odd]
    push_cast; nlinarith [Nat.cast_nonneg (α := ℤ) j]

/-- **Upper growth bound.** `8·gpAt n ≤ 3n² + 4n + 1` for every `n`, with equality at
odd positions.  Hence `gpAt n ≤ (3n²+4n+1)/8`. -/
theorem gpAt_eight_upper (n : ℕ) : 8 * gpAt n ≤ 3 * (n : ℤ) ^ 2 + 4 * n + 1 := by
  rcases Nat.even_or_odd n with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [show j + j = 2 * j from (two_mul j).symm, gpAt_eight_even]
    push_cast; nlinarith [Nat.cast_nonneg (α := ℤ) j]
  · rw [gpAt_eight_odd]
    push_cast; nlinarith [Nat.cast_nonneg (α := ℤ) j]

/-- **Clean quadratic upper bound.** `8·gpAt n ≤ 3(n+1)²`, a tidy consequence of
`gpAt_eight_upper` (`3n²+4n+1 ≤ 3n²+6n+3`). -/
theorem gpAt_eight_upper' (n : ℕ) : 8 * gpAt n ≤ 3 * ((n : ℤ) + 1) ^ 2 := by
  have h := gpAt_eight_upper n
  nlinarith [Nat.cast_nonneg (α := ℤ) n]

/-- **Growth sandwich (`gpAt n = Θ(n²)`).** The enumeration is squeezed between two
quadratics in `n`: `3n² ≤ 8·gpAt n ≤ 3n²+4n+1`.  So the `n`-th generalized pentagonal
number is `(3/8)n² + O(n)`. -/
theorem gpAt_eight_sandwich (n : ℕ) :
    3 * (n : ℤ) ^ 2 ≤ 8 * gpAt n ∧ 8 * gpAt n ≤ 3 * (n : ℤ) ^ 2 + 4 * n + 1 :=
  ⟨gpAt_eight_lower n, gpAt_eight_upper n⟩

/-- **Density / sparsity of A001318.** If the `n`-th generalized pentagonal number does
not exceed `N`, then `3n² ≤ 8N`, i.e. `n ≤ √(8N/3)`.  Since `gpAt` enumerates the
generalized pentagonal numbers in increasing order (`gpAt_enumerates`), this bounds how
many of them can lie in `[0, N]`: at most `√(8N/3) + 1`.  They thin out like `√N`. -/
theorem gpAt_le_imp_index_sq_le {n : ℕ} {N : ℤ} (h : gpAt n ≤ N) :
    3 * (n : ℤ) ^ 2 ≤ 8 * N := by
  have hlow := gpAt_eight_lower n
  linarith

end PentagonalNumberTheoremOQ01OQ01
